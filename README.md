<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# fft

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/fft/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/fft/actions/workflows/docker-action.yml




This repository contains Coq-proofs about the Fast Fourier Transform

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.20 or later
- Additional dependencies:
  - [Bignums](https://github.com/coq/bignums) same version as Coq
  - [MathComp ssreflect 2.4 or later](https://math-comp.github.io)
  - [Flocq 4.2.1 or later](https://gitlab.inria.fr/flocq/flocq.git)
  - [Interval 4.11.1 or later](https://gitlab.inria.fr/coqinterval/interval)
  - [Coquelicot 3.4.3 or later](https://gitlab.inria.fr/coquelicot/coquelicot)
- Coq namespace: `fft`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of fft
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-fft
```

To instead build and install manually, do:

``` shell
git clone https://github.com/thery/fft.git
cd fft
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



