Before you run the scripts here, ensure that you have run the `setup.py` script within the main directory (or manually edited the absolute paths). 

This directory contains code to prove the main Theorems of our paper. Due to transformations being called from relative directories, you need to be in this directory to run the scripts. A short description of each file follows:
  - `1-1-thm.m` proves Theorem 1.1 (after one grants that the transformations in Theorem 1.5 give the transformed conic and cubic -- these may be accessed via ). 
  - `1-5-thm_qD.m` proves Theorem 1.5 in the case of $q_D$ (excepting when $D = 17$).
  - `1-5-thm_pD.m` proves Theorem 1.5 in the case of $p_D$ for $D \leq 17$.
    - It takes about an hour to run `1-5-thm_pD.m` due to the naive way in which the transformations are stored. If you wish only to verify the conics, then commenting out any line with `M` will speed up the calcuations markedly.
  - `1-2-coros_fD.m` prove Corollaries 1.2, 1.3, and 7.1 where we compute the functions $f_D(a,b,c; x)$ for which $C : y^2 = f_D(a,b,c; x)$.

A short description of each of the subdirectories:
  - `trans/` contains the trasformations required to compute $q_D$.
    - `coord-change/` contains an initial coordinate change on the base ring of the conic $L_D$ which is required to be run before `trans/` will be the correct change (see `1-5-thm_pD.m`).
  - `trans-rat/` contains the transformations required to compute $p_D$.
  - `conic-param/` contains parametrisations of the conics $\mathcal{L}_D$ over the field $\mathbb{Q}(\mathscr{L}_D)$.
  - `3fold-param/` contains parametrisations for the 3-folds $r^2 - Ds^2 - p_D$ for each $D \leq 13$.
  