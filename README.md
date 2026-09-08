<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# PP M1 2026-2027 -- Rocq Tutorial






A [tutorial](theories/tutorial.v) for PP M1 2026-2027

## Meta

- Author(s):
  - Cyril Cohen (initial)
- License: [GNU Lesser General Public License v2.1](LICENSE)
- Additional dependencies:
  - Mathematical components version 2.5.0
  - Mathematical components algebra tactics 1.2.7
  - Mathematical components zify plugin 1.6.0+2.0+8.18
  - Mathematical components analysis library 1.16.0
- Rocq/Coq namespace: `PPM1`
- Related publication(s): none

## Building and installation instructions

### Favorite option for this tutorial: codespaces

[Start codespaces](https://github.com/codespaces/new)

### Local installation

#### using opam
After having installed opam and configured it for Coq [cf official
doc](https://coq.inria.fr/opam-using.html), run:
```bash
opam install --deps-only .
make
```
You can now run your favorite editor, you may need to install your
favorite language server (i.e. `opam install coq-lsp` or
`opam install vsrocq-language-server`)

#### Using nix
After [installing nix](https://nixos.org/download/) and
[cachix](https://docs.cachix.org/installation), run once:
```bash
cachix use coq
cachix use coq-community
cachix use math-comp
cachix use cohencyril
```

Then, every time you want to use it you need to run (may take a few
minutes the first time)
```bash
nix-shell
make
```
You can now run your favorite editor, you **do not need** to install your
favorite language server (they are included in the shell)

#### Using docker (warning, the image is > 17GB)

You need to [install docker](https://docs.docker.com/engine/install/).

Then start vscode with the
[`devcontainer`](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers)
extension, then click on "reopen in container" (or `F1` and type the latter).

## Documentation

Follow the [tutorial](theories/tutorial.v).
