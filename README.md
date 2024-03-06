This is the GitHub repository containing code related to the paper [*Generic models for genus 2 curves with real multiplication*](https://arxiv.org/abs/2403.03191) by Alex Cowan, Sam Frengley, and Kimball Martin [arXiv:2403.03191](https://arxiv.org/abs/2403.03191).

Most of the code in this repository is written in [`Magma`](http://magma.maths.usyd.edu.au/magma/) though many of the files should be written in such a way as to be acessible to most computer algebra systems.

## Using the intrinsics in `models`
To be able to use the provided `Magma` intrinsics within the `models` directory the user should first run `setup.py` with Python 3 (tested on Python 3.8.10 and Python 3.10.12). This short script edits a few absolute paths so that the relevant `spec` files can be attached in a directory independent fashion.

Alternatively you can simply edit the first lines of each of the `.m` files in `models` to contain the correct absolute path.

## Directory structure
- `minimize` contains code for our minimization algorithm as described in Section 5 of the paper. Notable files within this directory are `minimization.m` which contains the minimization code and `ICmestre.m` which contains the IC and RM simplified Mestre conics. The main intrinsic we provide is:
  - `MinimizationSearch` which runs Algorithm 5.5.

- `models` contains the equations for the varieties in the paper (be they the genus 2 curves, the conics, or the 3-folds). Further information about where one can find which equations can be found in the README `models/README.md`. Notable intrinsics provided by the `models/spec` specification file are documented at `models/README.md`:
  - `RMWeierstrassEquationRational`
  - `RMWeierstrassEquation`

- `proofs` verifies computational claims in the paper and stores the requisite transformations to prove Theorems 1.1 and 1.5.

- `tests` contains several files testing the functionality provided by this repository:
  - We give examples for using `MinimizationSearch`
  - We give some sanity checks (using `AnalyticJacobian`) for the existence of an endomorphism of $\mathrm{Jac}(C)$ with discriminant $D$.
