/**************************************************
  FUNCTIONS FOR CHANGING COORDINATES
**************************************************/

intrinsic DifferentCoords(pi::RngMPolElt) -> SeqEnum
{
Suggests good coordinate changes to make pi better for our purposes. 
INPUT: A homogeneous polynomial π
}
  pi2, M := MinRedTernaryForm(pi);
  C := Curve(Proj(Parent(pi2)), pi2);
  S := SingularPoints(C);

  SS := [s : s in Subsets({a : a in S}, 2)];
  
  mults := func<s1 | &+[Multiplicity(s) : s in s1]>;
  
  m := Max([mults(s) : s in SS]);
  SS := [s : s in SS | mults(s) eq m];

  M2s := [];
  
  for s in SS do
    ss := [Eltseq(x) : x in s];
    line := KernelMatrix(Matrix(Rationals(), 3, 2, [[ss[i][j] : i in [1..2]] : j in [1..3]]));
    line := Eltseq(line);
    if line[3] ne 0 then
      M2 := Matrix(Rationals(), 3, 3, [[1,0,0], [0,1,0], line]);
    elif line[2] ne 0 then
      M2 := Matrix(Rationals(), 3, 3, [[0,0,1], [1,0,0], line]);
    elif line[1] ne 0 then
      M2 := Matrix(Rationals(), 3, 3, [[0,1,0], [0,0,1], line]);
    end if;
    Append(~M2s, M2^(-1));
  end for;
  
  return [M*M2 : M2 in M2s];
end intrinsic;


intrinsic FindCoVs(L::RngMPolElt) -> SeqEnum
{
Find good changes of variables for L based on minimizing
discriminant and coefficient factors of degrees between 3 and 10
}
  R<g,h> := Parent(Numerator(Coefficients(L)[1]));
  S<a,b,c> := PolynomialRing(QQ,3);
  phi := hom< R -> S | a, b >;
  ratfacts, polyfacts := DiscFactors(L);
  covs := [];
  coeffs := [Numerator(coeff) : coeff in Coefficients(L)];
  polys := [f[1] : f in polyfacts];
  polys := polys cat coeffs;
  for f in polys do
    if Degree(f) ge 3 and Degree(f) le 10 then
      try
        f1 := Homogenization(phi(f),c);
        f2, M := MinRedTernaryForm(f1);
        Append(~covs, M);
        Ms := DifferentCoords(f1);
        covs := covs cat Ms;
      catch err
        e := 1;
      end try;
    end if;
  end for;
  return covs;
end intrinsic;


intrinsic FindCoVs2(invts::SeqEnum) -> SeqEnum
{
Find good changes of variables for a list of polynomials in ℚ(g,h)
}
  R<g,h> := Parent(Numerator(invts[1]));
  S<a,b,c> := PolynomialRing(QQ,3);
  phi := hom< R -> S | a, b >;
  covs := [];
  polys := [];
  for invt in [Numerator(f) : f in invts] do
    polys := polys cat [fact[1] : fact in Factorization(invt)];
  end for;
  for f in polys do
    if Degree(f) ge 3 then
      try
        f1 := Homogenization(phi(f),c);
        f2, M := MinRedTernaryForm(f1);
        Append(~covs, M);
        Ms := DifferentCoords(f1);
        covs := covs cat Ms;
      catch err
        e := 1;
      end try;
    end if;
  end for;
  return covs;
end intrinsic;


intrinsic VariableChange(L::RngMPolElt,M::AlgMatElt) -> RngMPolElt
{
Input: polynomial L in ℚ(g,h), invertible matrix M in M_3(ℚ)
Output: the resulting polynomial upon rational change of variables in (g,h) 
given by matrix M in PGL_3
}
  coeffs, monos := CoefficientsAndMonomials(L);
  n := #coeffs;
  R<g,h> := Parent(Numerator(coeffs[1]));
  S<a,b,c> := PolynomialRing(QQ,3);
  phi := hom< R -> S | a, b >;
  phiinv := hom< S -> R | g, h, 1 >;
  newcoeffs := [];
  for coeff in coeffs do
    f := Homogenization(phi(Numerator(coeff)),c);
    fdenom := Homogenization(phi(Denominator(coeff)),c);
    f := f^M;
    fdenom := fdenom^M;
    Append(~newcoeffs, phiinv(f)/phiinv(fdenom));
  end for;
  newL := Parent(L)!0;
  for i in [1..n] do
    newL := newL + newcoeffs[i]*monos[i];
  end for;
  return newL;
end intrinsic;


intrinsic TryCoVs(branch::Any : fwd:=false) -> Any
{
This intrinsic makes a linear change of variables to the base ring ℚ(t1,t2) based on the 
FindCoVs strategy above. It creates new branches based on this. This is not used in our
minimization algorithms as implemented, but is given here for users if they wish to try it.
}
  L := branch`pol;
  covs := FindCoVs(L);
  nodes := [];
  for M in covs do
    L2 := Rescale(VariableChange(L,M));
    if not IsSing(L2) then
      nn := rec< Node | pol:=L2>; 
      nn`scores := Append(branch`scores, NodeScore(L2 : fwd := fwd));
      nn`trans := branch`trans cat [[M,M]];
      Append(~nodes,nn);
    end if;
  end for;
  return nodes;
end intrinsic;
