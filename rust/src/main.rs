//! ``skijack FILE`` -- the whole pipeline from the command line, one flag
//! per view, matching the reference CLI's output byte for byte.

use std::io::Write;
use std::process::ExitCode;

use skijack::ast::Fuel;
use skijack::check::check_program;
use skijack::dictionary::{from_expansion, lift, structural_hash, MIN_LIFT_SIZE};
use skijack::errors::{repr, SkijackError};
use skijack::expand::{expand_program, PRELUDE_NAMES};
use skijack::lexicon::Lexicon;
use skijack::parser::parse;
use skijack::render::{render_expr, render_program};
use skijack::run::{decode, peel, run_level1, run_policy, DEFAULT_CAP};
use skijack::term::pretty;
use skijack::typecheck::typecheck_program;

struct Args {
    file: String,
    lexicon: String,
    check: bool,
    expand: bool,
    lift: Option<String>,
    dictionary: bool,
    render: Option<String>,
    run: Option<String>,
    fuel: Option<usize>,
    max_steps: usize,
}

const USAGE: &str = "usage: skijack [-h] [--lexicon {auto,ascii,unicode}] [--check] [--expand] [--lift NAME] \
[--dictionary] [--render LEXICON] [--run NAME] [--fuel FUEL] [--max-steps MAX_STEPS] file";

fn usage_error(msg: &str) -> ExitCode {
    eprintln!("{}\nskijack: error: {}", USAGE, msg);
    ExitCode::from(2)
}

fn parse_args() -> Result<Args, ExitCode> {
    let mut args = Args {
        file: String::new(),
        lexicon: "auto".to_string(),
        check: false,
        expand: false,
        lift: None,
        dictionary: false,
        render: None,
        run: None,
        fuel: None,
        max_steps: 5_000_000,
    };
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let mut i = 0;
    let mut file: Option<String> = None;
    let take = |i: &mut usize, name: &str| -> Result<String, ExitCode> {
        *i += 1;
        argv.get(*i).cloned().ok_or_else(|| usage_error(&format!("argument {}: expected one argument", name)))
    };
    while i < argv.len() {
        let arg = argv[i].as_str();
        let (flag, inline): (&str, Option<String>) = match arg.split_once('=') {
            Some((f, v)) if f.starts_with("--") => (f, Some(v.to_string())),
            _ => (arg, None),
        };
        let value = |i: &mut usize| -> Result<String, ExitCode> {
            match &inline {
                Some(v) => Ok(v.clone()),
                None => take(i, flag),
            }
        };
        match flag {
            "-h" | "--help" => {
                println!("{}\n\ncompile, check, render, lift and run a .ski program", USAGE);
                return Err(ExitCode::SUCCESS);
            }
            "--lexicon" => {
                let v = value(&mut i)?;
                if !["auto", "ascii", "unicode"].contains(&v.as_str()) {
                    return Err(usage_error(&format!(
                        "argument --lexicon: invalid choice: {} (choose from 'auto', 'ascii', 'unicode')",
                        repr(&v)
                    )));
                }
                args.lexicon = v;
            }
            "--check" => args.check = true,
            "--expand" => args.expand = true,
            "--dictionary" => args.dictionary = true,
            "--lift" => args.lift = Some(value(&mut i)?),
            "--render" => {
                let v = value(&mut i)?;
                if !["ascii", "unicode"].contains(&v.as_str()) {
                    return Err(usage_error(&format!(
                        "argument --render: invalid choice: {} (choose from 'ascii', 'unicode')",
                        repr(&v)
                    )));
                }
                args.render = Some(v);
            }
            "--run" => args.run = Some(value(&mut i)?),
            "--fuel" => {
                let v = value(&mut i)?;
                args.fuel = Some(v.parse().map_err(|_| usage_error(&format!("argument --fuel: invalid int value: {}", repr(&v))))?);
            }
            "--max-steps" => {
                let v = value(&mut i)?;
                args.max_steps = v.parse().map_err(|_| usage_error(&format!("argument --max-steps: invalid int value: {}", repr(&v))))?;
            }
            _ if arg.starts_with('-') && arg.len() > 1 => {
                return Err(usage_error(&format!("unrecognized arguments: {}", arg)));
            }
            _ => {
                if file.is_some() {
                    return Err(usage_error(&format!("unrecognized arguments: {}", arg)));
                }
                file = Some(arg.to_string());
            }
        }
        i += 1;
    }
    match file {
        Some(f) => {
            args.file = f;
            Ok(args)
        }
        None => Err(usage_error("the following arguments are required: file")),
    }
}

fn lexicon_of(path: &str, given: &str) -> Lexicon {
    match given {
        "ascii" => Lexicon::Ascii,
        "unicode" => Lexicon::Unicode,
        _ => {
            if path.contains(".unicode.") {
                Lexicon::Unicode
            } else {
                Lexicon::Ascii
            }
        }
    }
}

fn read_source(path: &str) -> Result<String, String> {
    let bytes = std::fs::read(path).map_err(|e| {
        let s = e.to_string();
        match s.find(" (os error") {
            Some(i) => s[..i].to_string(),
            None => s,
        }
    })?;
    String::from_utf8(bytes).map_err(|_| "not valid UTF-8".to_string())
}

fn run(args: &Args, out: &mut impl Write, err: &mut impl Write) -> Result<u8, SkijackError> {
    let lx = lexicon_of(&args.file, &args.lexicon);
    let text = match read_source(&args.file) {
        Ok(t) => t,
        Err(m) => {
            writeln!(err, "{}: {}", args.file, m).ok();
            return Ok(1);
        }
    };
    let program = parse(&text, lx)?;

    if let Some(r) = &args.render {
        let rlx = Lexicon::parse(r).unwrap();
        write!(out, "{}", render_program(&program, rlx)).ok();
        return Ok(0);
    }

    let problems = check_program(&program, &PRELUDE_NAMES);
    if args.check {
        if !problems.is_empty() {
            for p in &problems {
                writeln!(err, "{}: {}", args.file, p).ok();
            }
            return Ok(1);
        }
        writeln!(out, "{}: Stage A clean", args.file).ok();
        let problems = typecheck_program(&program, &PRELUDE_NAMES, false)?;
        if !problems.is_empty() {
            for p in &problems {
                writeln!(err, "{}: {}", args.file, p).ok();
            }
            return Ok(1);
        }
        writeln!(out, "{}: Stage B clean", args.file).ok();
        return Ok(0);
    }
    if !problems.is_empty() {
        for p in &problems {
            writeln!(err, "{}: {}", args.file, p).ok();
        }
        return Ok(1);
    }

    let mut exp = expand_program(&program, true, true)?;

    if args.expand {
        let mut names: Vec<&String> = exp.terms.keys().collect();
        names.sort();
        for name in names {
            writeln!(out, "{:8}  {:24} {}", exp.sizes[name], name, pretty(&exp.terms[name])).ok();
        }
        return Ok(0);
    }

    if args.dictionary {
        let d = from_expansion(&mut exp)?;
        writeln!(out, "# {}: {} entries", d.version, d.len()).ok();
        for (name, atoms, h) in d.rows() {
            writeln!(out, "{:8}  {:24} {}", atoms, name, h).ok();
        }
        return Ok(0);
    }

    if let Some(name) = &args.lift {
        let Some(target) = exp.terms.get(name).cloned() else {
            writeln!(err, "{}: no term named {}", args.file, repr(name)).ok();
            return Ok(1);
        };
        let d = from_expansion(&mut exp)?;
        let th = structural_hash(&target);
        let whole: Vec<String> = d.names().into_iter().filter(|n| d.get(n).unwrap().hash == th).collect();
        writeln!(out, "{}", render_expr(&lift(&target, &d, MIN_LIFT_SIZE, &whole), lx)).ok();
        return Ok(0);
    }

    if let Some(name) = &args.run {
        let Some(prog) = exp.level1.get(name).cloned() else {
            if let Some(t) = exp.terms.get(name) {
                writeln!(out, "{:8}  {}", exp.sizes[name], pretty(t)).ok();
                return Ok(0);
            }
            writeln!(err, "{}: no declaration named {}", args.file, repr(name)).ok();
            return Ok(1);
        };
        if prog.fuel == Fuel::Policy && args.fuel.is_none() {
            let r = run_policy(&prog, 8, DEFAULT_CAP, args.max_steps)?;
            let budget = match r.budget {
                Some(b) => b.to_string(),
                None => "cap".to_string(),
            };
            let payload = match r.payload() {
                None => String::new(),
                Some(p) => format!(" {}", render_expr(&decode(p, &prog.object_type, 1_000_000, 200_000)?, lx)),
            };
            writeln!(out, "{}{}   (budget {}, {} contractions)", r.constructor, payload, budget, r.steps).ok();
            return Ok(0);
        }
        let o = run_level1(&prog, args.max_steps, args.fuel)?;
        if !o.whnf() {
            writeln!(err, "{} after {} contractions", o.status.value(), o.steps).ok();
            return Ok(1);
        }
        let (ctor, fields) = peel(&o.term, &prog.result_type, args.max_steps)?;
        let payload = match fields.first() {
            None => String::new(),
            Some(f) => format!(" {}", render_expr(&decode(f, &prog.object_type, args.max_steps, 200_000)?, lx)),
        };
        writeln!(out, "{}{}   ({} contractions)", ctor, payload, o.steps).ok();
        return Ok(0);
    }

    // no flag: a summary
    writeln!(out, "{}: {}, {} declarations, Stage A clean", args.file, lx, program.decls.len()).ok();
    writeln!(out, "  {} compiled terms, {} level-1 declaration(s)", exp.terms.len(), exp.level1.len()).ok();
    let mut names: Vec<&String> = exp.level1.keys().collect();
    names.sort();
    for name in names {
        let lp = &exp.level1[name];
        let fuel = match &lp.fuel {
            Fuel::N(n) => n.to_string(),
            Fuel::Policy => "policy".to_string(),
        };
        writeln!(out, "    {} = {} @ {}", name, lp.interp, fuel).ok();
    }
    Ok(0)
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(a) => a,
        Err(code) => return code,
    };
    // deep terms want a deep stack
    let handle = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let stdout = std::io::stdout();
            let stderr = std::io::stderr();
            let mut out = std::io::BufWriter::new(stdout.lock());
            let mut err = stderr.lock();
            let code = match run(&args, &mut out, &mut err) {
                Ok(c) => c,
                Err(e) => {
                    out.flush().ok();
                    writeln!(err, "{}: {}", args.file, e).ok();
                    1
                }
            };
            out.flush().ok();
            code
        })
        .expect("spawn");
    ExitCode::from(handle.join().unwrap_or(1))
}
