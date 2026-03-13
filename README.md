# Mahsa_Ansari_Thesis

This repository contains the Maple code and benchmark files used in my thesis on computing monic GCDs and resultants of multivariate polynomials over algebraic number field 
    $Q(\alpha_1,\ldots,\alpha_n)$.

## Overview

The repository includes benchmark programs for comparing algorithms under two types of experiments:

### 1. DF Benchmark
In this benchmark, we vary the degree of the algebraic number field:
dF := [4, 8, 16, 24, 32, 64, 128, 256, 512, 1024]
### 2. TD Benchmark
In this benchmark, we vary the total degree of the input polynomials and the GCD ( g ).
Here,
* (\deg(f_1) = \deg(f_2)),
* (\deg(g) = \deg(f_1)/2).
These experiments are performed over two algebraic number fields: one of degree 32 and one of degree 64. In the thesis, I included the benchmark over the degree 64 field.

## Repository Contents

The main files in this repository are:

* `MGCD_recden`
* `MGCD_RDP`
* `MRS`

Each of these contains benchmark code used in the thesis.

## 1. `MGCD_recden`
In this file, computations are performed over Q(\alpha_1, \ldots, \alpha_n) using the `recden` library. The following subalgorithms are included:
### `LAminpoly`
Computes the generator polynomial M(z) s.t
\bar{L}_p = Z_p[z]/\langle m(z) \rangle \cong L_p = Z_p[z_1, \ldots, z_n]/\langle M_1, \ldots, M_n \rangle .
It also contains the isomorphism `Phi`, which converts polynomials between ( L_p ) and ( \bar{L}_p ).
### `lm`
Contains code for computing:
* the leading monomial,
* the denominator,
* the semi-associate 
of a polynomial.
### `MGCD1`
Computes the monic GCD of two polynomials in Q(\alpha_1, \ldots, \alpha_n)[x_1, \ldots, x_k] using `LAminpoly`.
### `MGCD2`
Computes the monic GCD of two polynomials in Q(\alpha_1, \ldots, \alpha_n)[x_1, \ldots, x_k] without using `LAminpoly`.
### `PGCD`
Computes the monic GCD of two polynomials in \bar{L}_p[x_1, \ldots, x_k].
### `Min_creat`
Creates a list of minimal polynomials for an algebraic number of degree `N` with `numext` extensions.
### `recden`
Contains the core code for computation over
Q(\alpha_1, \ldots, \alpha_n)
****************************************************************************************************************
## 2. `MRS`
In this file, computations are performed over Q(\alpha_1, \ldots, \alpha_n) using the Maple library  RDP := Algebraic:-RecursiveDensePolynomials
The following subalgorithms are included:
### `Get`
Contains the code from `recden` that is not available in the RDP library but is needed by these implementations.
### `MRES1`
Computes the resultant of two polynomials in Q(\alpha_1, \ldots, \alpha_n)[x_1, \ldots, x_k]
using `LAminpoly`.
### `MRES2`
Computes the resultant of two polynomials in Q(\alpha_1, \ldots, \alpha_n)[x_1, \ldots, x_k] without using `LAminpoly`.
### `PRES`
Computes the resultant of two polynomials in \bar{L}_p[x_1, \ldots, x_k].
### `URES`
Computes the resultant of two univariate polynomials in \bar{L}_p[x_1].
****************************************************************************************************************
## 3. `MGCD_RDP`
In this file, computations are performed over Q(\alpha_1, \ldots, \alpha_n) using the Maple library
RDP := Algebraic:-RecursiveDensePolynomials
****************************************************************************************************************
## Note on Benchmark Comparisons
The RDP library already includes optimized routines for computing GCDs over Q(\alpha_1, \ldots, \alpha_n).
For this reason, the benchmark results in `MGCD_RDP` are not fair and not directly comparable to those in `MGCD_recden`.
In the thesis, I included the benchmark results from `MGCD_recden`.
