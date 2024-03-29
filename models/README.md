Note that in these (sub)-directories `.txt` files should be easily loaded into any reasonable computer algebra system whereas the `.m` files have some `Magma`-specific syntax (and should be opened up and edited if you want to load them elsewhere).

## Sub-directories 
The storage sub-directories are arranged as follows:
- Files `F_zghrs/D.txt` store Weierstrass models of the form $F_D(g,h,z,r,s; x)$ where you need the relations $z^2 = \lambda_D$ and $r^2 - Ds^2 = q_D$.
- Files `f_abc/D.txt` store Weierstrass models of the form $f_D(a,b,c; x)$ in the rational cases. Here $a,b,c$ are free (but triples may correspond to the same curve).
  - Note that when $D = 17$ there are only two parameters $a,b$.
  - Note that when $D = 33$ there are instead three parameters $g,h,z$ which must satisfy $z^2 = \lambda_{33}$.
  - Note that when $D > 17$ is not $33$ there are four parameters $\zeta,a,b,c$ which must satisfy $\zeta^2 = \Lambda_{D}$. 
- Files `q/D.txt` store the polynomials $q_D \in \mathbb{Q}(Y_{-}(D))$ for each $D$ in Theorem 1.5.
- Files `p/D.txt` store the polynomials $p_D \in \mathbb{Q}(Y_{-}(D))$ for each $D \leq 17$.
- Files `xi_and_phi/D/xi.txt` (resp. `xi_and_phi/D/phi.txt`) store cubic (resp. quadratic) polynomials such that $f_D = \mathrm{Nm}_{L/k}(\varphi_D)$ where $L = k[x]/\xi(x)$.
- File `lambda/D.txt` and `Lambda_abc/D.txt` store respectively the polynomials $\lambda_D$ (of Elkies--Kumar) and $\Lambda_D$ (from the discussion leading to Question 1.7).
- Files `RM_invs/D.txt` and `IC_invs/D.txt` store Elkies--Kumar's RM $(A,A_1,B,B_1,B2)$ and Igusa--Clebsch invariants for the Humbert surface of discriminant $D$.

## Intrinsics provided by `spec`
The main intrinsics are:
- `RMWeierstrassEquationRational` outputs the degree 6 polynomial $f_D(a,b,c;x)$. Parameters are:
  - `D` a discrimiant $\leq 17$.
  - `abc` a sequence of length 3 or 2 if `D` is, resp. isn't, 17.
- `RMWeierstrassEquation` outputs a Weierstrass equation corresponding to a point on a Humbert surface. Parameters are:
  - `D` a discrimiant $\leq 61$ which we computed for.
  - `g` and `h` giving a point on the Humbert surface.
  - `extend_base:=false` a boolean governing if we are willing to base change to allow a model.
- `RMWeierstrassEquation` outputs a Weierstrass equation corresponding to a point on a the conic bundle $\mathscr{L}_D$. Parameters are:
  - `D` a discrimiant $\leq 61$ which we computed for.
  - `z`, `g`, `h`, `r`, `s` giving a point on the conic bundle $\mathscr{L}_D$.
- `RMWeierstrassEquationLambda` outputs a Weierstrass equation corresponding to a point satisfying $z^2 = \Lambda_D$. Parameters are:
  - `D` a discrimiant $21 \leq D \leq 61$ with $D \neq 24$.
  - `z`, `a`, `b`, `c` satisfying the relation $z^2 = \Lambda_D(a,b,c)$.  

The following intrinsics access the stored data, and take as input a discriminant $D$. All also take in an option argument `coords` (the coordinates of the base). More information is provided in `get-polynomials.m`.
- `Getq_D`
- `Getp_D`
- `Get_xi_phi`
- `Getlambda_D`
- `GetUpperLambda_D`
- `GetTransformedMestreConic`
  - `rat:=false`: a Boolean which for rational discriminants toggles on whether you are using the $m,n$ coordinates.
- `GetTransformedMestreCubic`
  - `rat:=false`: a Boolean which for rational discriminants toggles on whether you are using the $m,n$ coordinates.
- `GetHMSParam` 