<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# fft

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/fft/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/fft/actions/workflows/docker-action.yml




This repository contains Coq-proofs about FFT algorithm

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.20 or later
- Additional dependencies:
  - [Bignums](https://github.com/coq/bignums) same version as Coq
  - [MathComp ssreflect 2.3 or later](https://math-comp.github.io)
  - [Flocq 4.1.3 or later](https://gitlab.inria.fr/flocq/flocq.git)
  - [Interval 4.11.1 or later](https://gitlab.inria.fr/coqinterval/interval)
  - [Coquelicot 3.4.2 or later](https://gitlab.inria.fr/coquelicot/coquelicot)
- Coq namespace: `fft`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/fft.git
cd fft
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



