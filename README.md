<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Fft

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/fft/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/thery/fft/actions/workflows/docker-action.yml




This repository contains Rocq proofs about the Fast Fourier Transform

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Additional dependencies:
  - [Bignums](https://github.com/coq/bignums) same version as Rocq
  - [MathComp ssreflect 2.6 or later](https://math-comp.github.io)
  - [MathComp algebra 2.6 or later](https://math-comp.github.io)
  - [Flocq 4.2.2 or later](https://gitlab.inria.fr/flocq/flocq.git)
  - [Interval 4.11.5 or later](https://gitlab.inria.fr/coqinterval/interval)
  - [Coquelicot 3.4.5 or later](https://gitlab.inria.fr/coquelicot/coquelicot)
- Rocq/Coq namespace: `fft`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Fft
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-fft
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/thery/fft.git
cd fft
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



