<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Fft

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/fft/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/fft/actions/workflows/docker-action.yml




This repository contains Rocq-proofs about the Fast Fourier Transform

```coq
Fixpoint fft (n : nat) (w : R) (p : {poly R}) : {poly R} := 
if n is n1.+1 then
  let ev := fft n1 (w ^+ 2) (even_poly p) in
  let ov := fft n1 (w ^+ 2) (odd_poly p) in
  \poly_(i < 2 ^ n1.+1) let j := (i %% 2 ^ n1)%N in ev`_j + ov`_ j * w ^+ i 
else (p`_0)%:P.
```

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

To build and install manually, you need to make sure that all the
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



