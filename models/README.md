Note that in these (sub)-directories `.txt` files should be easily loaded into any reasonable computer algebra system whereas the `.m` files have some `Magma`-specific syntax (and should be opened up and edited if you want to load them elsewhere).

## Sub-directories 
The storage sub-directories are arranged as follows:
- Files `F/D.txt` store Weierstrass models of the form $F_D(g,h,z,r,s; x)$ where you need the relations $z^2 = \lambda_D$ and $r^2 - Ds^2 = q_D$.
- Files `F_hilb/D.txt` store Weierstrass models of the form $F_D(m,n,r,s; x)$ in the rational cases. You need the relation $r^2 - Ds^2 = p_D$.
- Files `f/D.txt` store Weierstrass models of the form $f_D(a,b,c; x)$ in the rational cases. Here $a,b,c$ are free (but triples may correspond to the same curve).
  - Note that when $D = 33$ there are instead three parameters $g,h,z$ which must satisfy $z^2 = \lambda_{33}$.
- Files `q/D.txt` store the polynomials $q_D \in \mathbb{Q}(Y_{-}(D))$ for each $D$ in Theorem 1.5.
- Files `p/D.txt` store the polynomials $p_D \in \mathbb{Q}(Y_{-}(D))$ for each $D \leq 17$.
- Files `xi_and_phi/D/xi.txt` (resp. `xi_and_phi/D/phi.txt`) store cubic (resp. quadratic) polynomials such that $f_D = \mathrm{Nm}_{L/k}(\varphi_D)$ where $L = k[x]/\xi(x)$.
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

The following intrinsics access the stored data, and take as input a discriminant $D$. All also take in an option argument `coords` (the coordinates of the base). More information is provided in `get-polynomials.m`.
- `Getq_D`
- `Getp_D`
- `Getlambda_D`
- `Get_xi_phi`
- `GetTransformedMestreConic`
  - `rat:=false`: a Boolean which for rational discriminants toggles on whether you are using the $m,n$ coordinates.
- `GetTransformedMestreCubic`
  - `rat:=false`: a Boolean which for rational discriminants toggles on whether you are using the $m,n$ coordinates.
- `GetHMSParam` 