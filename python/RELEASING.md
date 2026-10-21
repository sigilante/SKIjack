# Releasing `skijack`

The version lives in exactly one place, `skijack/_version.py`, read
statically by the build backend. Nothing else needs editing.

## Before tagging

```sh
python3 -m pytest -q                      # the oracle present
SKIJACK_ARTIFACT_DIR=/nonexistent SKIJACK_ALLOW_SKIP=1 \
  python3 -m pytest -q                    # 203 more skipped, deliberately
AVON=/path/to/avon python3 -m pytest -q   # the front ends too
```

The second run is the one a stranger without the artifact gets. It must
pass, and it must skip exactly 203 more tests than the first: those are
the cross-checks against the companion paper's artifact, and if they
vanish without the `SKIJACK_ALLOW_SKIP` opt-out something has broken the
guard in `tests/conftest.py`. Without `AVON`, the front ends' tests skip
in every run; the third runs them in Avon.

Then confirm the claims the package exists to support still hold:

```sh
skijack skijack/corpus/interp-whnff.ascii.ski --expand | grep -w whnfF   # 618
skijack skijack/corpus/scry-ns.ascii.ski --run answer   # RValN K   (28661 contractions)
```

## Build and check

```sh
rm -rf dist build
python3 -m build
python3 -m twine check dist/*
```

Both artifacts must pass. Confirm the wheel carries the corpus, since
an install without it is a compiler with no examples:

```sh
python3 -c "import zipfile; z=zipfile.ZipFile('dist/skijack-$(python3 -c '
import skijack._version as v; print(v.__version__)')-py3-none-any.whl');
print(sum(1 for f in z.namelist() if f.endswith('.ski')))"   # 34
```

## Install clean and smoke test

Never publish without installing the built artifact into a fresh
environment first: the source tree hides missing package data.

```sh
python3 -m venv /tmp/skv && /tmp/skv/bin/pip install dist/skijack-*.whl
/tmp/skv/bin/skijack --help
/tmp/skv/bin/python -c "import skijack; from skijack import corpus; \
  print(skijack.compile(corpus.read('interp-whnff')).sizes['whnfF'])"   # 618
```

## Publish

```sh
python3 -m twine upload --repository testpypi dist/*   # rehearse first
python3 -m twine upload dist/*
git tag -a v$(python3 -c "import skijack._version as v; print(v.__version__)") -m "..."
```

## Versioning

The published dictionary carries its own version prefix
(`skijack.dictionary.VERSION`, currently `skijack-2`) and it is not the
package version. A change to a Tier 1 expansion, to the encoding, or to
the constructor-order rule is a change to *that* one, and by
`DESIDERATA.md` §5 it is a version change whether or not the package
version moves. `skijack/abi.py` says which parts are normative.
