/* 
Code to both automate and assist by-hand minimization of Mestre conics L over 
a polynomial ring ℚ(g,h)

Main intrinsic:

    MinimizationSearch(L : maxsteps:=100, method:="slope", randomization:=false);
      "method" can be one of the following strings:
        ----------------------------------------------------------------------------
        | "slope" (default) | Average slope score                                  |
        ----------------------------------------------------------------------------
        | "deg1"            | Degree score with linear penalty for number of times |
        |                   | this score appeared along this path                  |
        ----------------------------------------------------------------------------
        | "deg2"            | Degree score with square penalty for number of times |
        |                   | this score appeared along this path                  |
        ----------------------------------------------------------------------------
        | "alt"             | Alternate between slope and deg2                     |
        ----------------------------------------------------------------------------
        | "fwd"             | Forward-looking score (slow)                         |
        ----------------------------------------------------------------------------

*/

declare verbose ConicMinimize, 2;

QQ := Rationals();
ZZ := Integers();

Node := recformat< pol : RngMPolElt, scores, trans : SeqEnum >; 

/* 
  Output of MinimizationSearch is a Node N if successful, 
  or list of untried leaf nodes if unsuccessful within max steps

  For each node N in the output:
    - N`pol is the minimized conic
    - N`scores is a list of node scores on the search path
    - N`trans is a list of list of matrices describing the transformations
		   to carry out this minimization. These work in the following way:
         > if a sublist has a single matrix, just apply this matrix to L
         > if a sublist has 4 matrices, they correspond to transformations after
            switching affine patches back and forth in g then in h 
       (the intrinsic ApplyTrans will carry out these transformations)
*/

/**************************************************
  FUNCTIONS TO RESCALE CONICS IN A NICE WAY
**************************************************/

function DiagCoeffs(L)
  P2<x0,x1,x2> := Proj(Parent(L));
  diagmons := [x0^2, x1^2, x2^2]; 
  return [MonomialCoefficient(L,m) : m in diagmons];
end function;

function DiagDegrees(L)
  return [Degree(Numerator(c)) : c in DiagCoeffs(L)];
end function;

// return discriminant degree
// Assume L is integral
function ConicDenom(L);
  polydenom := LCM([Denominator(c) : c in Coefficients(L)]); 
  ratdenoms := [];
  for c in Coefficients(L) do
    Append(~ratdenoms,LCM([Denominator(a) : a in Coefficients(Numerator(c))]));
  end for;
  ratdenom := LCM([r : r in ratdenoms]);
  return ratdenom*polydenom;
end function;


function Rescale1(L)
  P2<x0,x1,x2> := Proj(Parent(L));
  K := Parent(Coefficients(L)[1]);
  diagmcs := DiagCoeffs(L);

  alpha := [K | 1, 1, 1];                                                     // first scale out diag denominators
  for i in [1..3] do
    dfacts := Factorization(Denominator(diagmcs[i]));
    ratdfacts := Factorization(LCM([Denominator(a) : a in Coefficients(Numerator(diagmcs[i]))]));
    for fact in dfacts do
      alpha[i] := alpha[i]*fact[1]^Ceiling(fact[2]/2);
    end for;
    for fact in ratdfacts do
      alpha[i] := alpha[i]*fact[1]^Ceiling(fact[2]/2);
    end for;
  end for;
  M0 := DiagonalMatrix(K, [alpha[i] : i in [1..3]]);
  L1 := L^M0;

  L1 := L1*ConicDenom(L1);                                                    // scale out remaining denoms from cross-terms

  alpha := [K | 1, 1, 1];                                                     // first scale poly factors for diag coeffs
  diagmcs := DiagCoeffs(L1);
  Mtemp := IdentityMatrix(K,3);
  for i in [1..3] do
    nfacts := Factorization(Numerator(diagmcs[i]));
    for fact in nfacts do		
      j := Floor(fact[2]/2);
      Mtemp[i][i] := 1/fact[1]^j;
      Ltemp := L1^Mtemp;
      while ConicDenom(Ltemp) ne 1 and j gt 0 do                              // require no denominators
        j := j-1;                                                             // introduced in cross-terms
        Mtemp[i][i] := 1/fact[1]^j;
        Ltemp := L1^Mtemp;
      end while;
      alpha[i] := alpha[i]/fact[1]^j;
    end for;
    Mtemp[i][i] := alpha[i];
  end for;
  M1 := DiagonalMatrix(K, [alpha[i] : i in [1..3]]);
  L2 := L1^M1;

  alpha := [K | 1, 1, 1];                                                     // scale out rational factors for diag coeffs
  diagmcs := DiagCoeffs(L2);
  Mtemp := IdentityMatrix(K,3);
  for i in [1..3] do
    nfacts := Factorization(GCD([Numerator(a) : a in Coefficients(Numerator(diagmcs[i]))]));
    for fact in nfacts do
      j := Floor(fact[2]/2);
      Mtemp[i][i] := 1/fact[1]^j;
      Ltemp := L2^Mtemp;
      while ConicDenom(Ltemp) ne 1 and j gt 0 do                              // require no denominators
        j := j-1;                                                             // introduced in cross-terms
        Mtemp[i][i] := 1/fact[1]^j;
        Ltemp := L2^Mtemp;
      end while;
      alpha[i] := alpha[i]/fact[1]^j;
    end for;
    Mtemp[i][i] := alpha[i];
  end for;
  M2 := DiagonalMatrix(K, [alpha[i] : i in [1..3]]);
  L3 := L2^M2;

  dd := DiagDegrees(L3);                                                      // permute so diag degrees increasing
  M3 := M0*M1*M2;
  if dd[1] gt dd[2] then
    M := PermutationMatrix(K, [ 2, 1, 3 ]);
    L3 := L3^M; M3 := M3*M;
  end if;
  dd := DiagDegrees(L3);
  if dd[2] gt dd[3] then
    M := PermutationMatrix(K, [ 1, 3, 2 ]);
    L3 := L3^M; M3 := M3*M;
  end if;
  dd := DiagDegrees(L3);
  if dd[1] gt dd[2] then
    M := PermutationMatrix(K, [ 2, 1, 3 ]);
    L3 := L3^M; M3 := M3*M;
  end if;

  return L3, M3;
end function;

function Rescale2(L)
  K := Parent(Coefficients(L)[1]);
  coeffs := [Numerator(c) : c in Coefficients(L)];
  d1 := GCD(coeffs);
  L1 := L/d1;
  mons := MonomialsOfDegree(Parent(L1), 2);
  coeffs := [Numerator(MonomialCoefficient(L1,mon)) : mon in mons];
  a11, a12, a13, a22, a23, a33 := Explode(coeffs);
  b3 := GCD([a11,a12,a22]);
  b2 := GCD([a11,a13,a33]);
  b1 := GCD([a22,a23,a33]);
  d2 := b1*b2*b3;
  M1 := DiagonalMatrix(K,[b1,b2,b3]);
  L2 := L1^M1/d2;

  coeffs := [Numerator(c) : c in Coefficients(L2)];
  ratcoeffs := [GCD([Numerator(a) : a in Coefficients(c)]) : c in coeffs];
  n1 := GCD(ratcoeffs);
  L3 := L2/n1;

  coeffs := [Numerator(MonomialCoefficient(L3,mon)) : mon in mons];
  ratcoeffs := [GCD([0] cat [Numerator(a) : a in Coefficients(c)]) : c in coeffs];
  a11, a12, a13, a22, a23, a33 := Explode(ratcoeffs);
  c3 := GCD([a11,a12,a22]);
  c2 := GCD([a11,a13,a33]);
  c1 := GCD([a22,a23,a33]);
  n2 := c1*c2*c3;
  M2 := DiagonalMatrix(K,[c1,c2,c3]);

  return L3^M2/n2, M1*M2;
end function;

intrinsic Rescale(L::RngMPolElt) -> RngMPolElt, AlgMatElt
{
Rescale L so that 
- all coefficients are integral (in ℤ[g,h])
- diagonal coefficients are squarefree
- any two diagonal coefficients have gcd 1
- diagonal degrees are ascending
}
  L1, M1 := Rescale1(L);
  d := ConicDenom(L1);
  require d eq 1: "WARNING: L1 has denominator";
  L2, M2 := Rescale2(L1);
  d := ConicDenom(L2);
  require d eq 1: "WARNING: L2 has denominator";
  return L2, M1*M2; 
end intrinsic;



/**************************************************
  VARIOUS HELPER FUNCTIONS FOR MINIMIZATION STEPS
**************************************************/

// Test whether the conic for L is singular
function IsSing(L);
  P2<x0,x1,x2> := Proj(Parent(L));
  try 
    bool := IsSingular(Conic(P2, L));
    if bool then
      print "WARNING: Transformation is singular!";
    end if;
    return bool;
  catch err
    return true;
  end try;
end function;

// return ℤ-part of discriminant Δ_ℚ(L)
function IntDisc(L);
  P2<x0,x1,x2> := Proj(Parent(L));
  D := Discriminant(Conic(P2, L));
  Dpol, Drat := FactNum(Numerator(D));
  return Drat;
end function;

// return discriminant degree
// Assume L is integral
function DiscDegree(L);
  P2<x0,x1,x2> := Proj(Parent(L));
  D := Discriminant(Conic(P2, L));
  return Degree(Numerator(D));
end function;

// return discriminant factors in 2 parts, rational factors and polynomial ones
// Assume L is integral
function DiscFactors(L);
  P2<x0,x1,x2> := Proj(Parent(L));
  D := Discriminant(Conic(P2, L));
  K := Parent(D);
  R := PolynomialRing(ZZ,2);
  D := R!Numerator(D);
  a := Factorisation(D);
  ratfacts := [ ];
  polyfacts := [ ];
  for fact in [u : u in a | Degree(u[1]) eq 0] do
    Append(~ratfacts, <Integers()!fact[1], fact[2]>);
  end for;
  for fact in [u : u in a | Degree(u[1]) ne 0] do
    Append(~polyfacts, <Numerator(Evaluate(fact[1], [K.1,K.2])), fact[2]>);
  end for;
  return ratfacts, polyfacts; 
end function;

// return square factors of discriminant 2 parts, rational factors 
// and polynomial ones
// Assume L is integral
function DiscSqFactors(L);
  sqratfacts := [];
  sqpolyfacts := [];
  ratfacts, polyfacts := DiscFactors(L);
  for fact in ratfacts do
    if fact[2] gt 1 then
      Append(~sqratfacts, fact); 
    end if;
  end for;
  for fact in polyfacts do
    if fact[2] gt 1 then
      Append(~sqpolyfacts, fact); 
    end if;
  end for;
  return sqratfacts, sqpolyfacts;
end function;

// given list of degrees [d1 <= d2 <= d3], return a list of permutations
// fixing this list
function StabS3(degs)
  d1, d2, d3 := Explode(degs);
  if d1 ne d2 and d2 ne d3 then
    return [[1,2,3]];
  end if;
  if d1 ne d2 and d2 eq d3 then
    return [[1,2,3], [1,3,2]];
  end if;
  if d1 eq d2 and d2 ne d3 then
    return [[1,2,3], [2,1,3]];
  end if;
  return [[1,2,3], [1,3,2], [2,1,3], [3,1,2], [2,3,1], [3,2,1]];
end function;

// diagonalize and rescale at last step
function DiagonalizeNode(node)
  L := node`pol;
  DC, Dmap := LegendreModel(Conic(Proj(Parent(L)),L));
  DM := Transpose(Matrix(Dmap)^(-1));
  L2 := L^DM;
  L3, M3 := Rescale(L2);
  nn := rec< Node | pol := L3>;
  nn`scores := node`scores;
  nn`trans := node`trans cat [[DM*M3]];
  return nn;
end function;


/**************************************************
  MAIN FUNCTIONS TO CARRY OUT MINIMIZATION STEPS
**************************************************/

intrinsic SingularSubschemeModPi(L::RngMPolElt, pi::RngIntElt : perm:=[1,2,3]) -> SeqEnum
{
Return singular subscheme of \bar(L)_π.
INPUT: Homogeneous degere 2 L and π an integer.
OUTPUT: List of (reduced) irred. components of singular locus of \bar(L)_π.
}
  KK := Parent(Coefficients(L)[1]);
  M := PermutationMatrix(KK,perm);
  Lperm := L^M;
  Ft<m,n> := FunctionField(GF(pi), 2);
  P2t := ProjectiveSpace(Ft, 2);
  f := EvaluateCoefficientsAndVars(Lperm, [m,n], [P2t.1, P2t.2, P2t.3]);
  S := Scheme(P2t, f);
  return SingularSS(S);
end intrinsic;


intrinsic SingularSubschemeModPi(L::RngMPolElt, pi::RngMPolElt : perm:=[1,2,3]) -> SeqEnum
{
Return singular subscheme of \bar(L)_π. 
INPUT: Homogeneous degere 2 L and π an element of ℚ[t1,t2]. 
OUTPUT: List of (reduced) irred. components of singular locus of \bar(L)_π.
}
  KK := Parent(Coefficients(L)[1]);
  M := PermutationMatrix(KK,perm);
  Lperm := L^M;

  flag := false;
  if IsUnivariate(Numerator(pi)) then
    bool, pol, j := IsUnivariate(Numerator(pi));
    if j eq 1 then
      flag := true;
    end if;
  end if;
  if flag then
    Qt<n> := FunctionField(QQ);
    Qt<m> := PolynomialRing(Qt);
    Qts<m> := quo<Qt | Evaluate(Numerator(pi), [m,n])>; 
    P2t := ProjectiveSpace(Qts, 2);
    f:= EvaluateCoefficientsAndVars(Lperm, [m,n], [P2t.1, P2t.2, P2t.3]);
    S := Scheme(P2t, f);
  else
    Qt<m> := FunctionField(QQ);
    Qt<n> := PolynomialRing(Qt);
    Qts<n> := quo<Qt | Evaluate(Numerator(pi), [m,n])>; 
    P2t := ProjectiveSpace(Qts, 2);
    f := EvaluateCoefficientsAndVars(Lperm, [m,n], [P2t.1, P2t.2, P2t.3]);
    S := Scheme(P2t, f);
  end if;

  return SingularSS(S);
end intrinsic;


function changebase(c,KK : switch := false)
  R := Parent(c);
  RR := Parent(Numerator(KK.1));
  if Type(R) eq FldFunRat then
    UU := PolynomialRing(ZZ,2);
    alpha := hom<Parent(Numerator(c)) -> UU | UU.1, UU.2>;
    beta := hom<UU -> RR | RR.1, RR.2>;
    return beta(alpha(Numerator(c)))/beta(alpha(Denominator(c)));
  end if;
  if Type(R) eq RngUPolRes then
    f := KK!0;
    S := PreimageRing(R);
    S0 := BaseRing(S);
    if not switch then
      alpha := hom<S0 -> KK | KK.1>;
      for m in Monomials(S!c) do
        f := f + alpha(MonomialCoefficient(S!c,m)) * (KK.2)^Degree(m);
      end for;
      return f;
    else
      alpha := hom<S0 -> KK | KK.2>;
      for m in Monomials(S!c) do
        f := f + alpha(MonomialCoefficient(S!c,m)) * (KK.1)^Degree(m);
      end for;
      return f;
    end if;
  end if;
end function;


intrinsic TransSingSubscheme(L::RngMPolElt,SS::Any : switch := false) -> Any, Any
{
Make a transformation with coordinates in ℤ[t1,t2] which moves the 
singular subscheme of \bar(L)_π to the origin.
}
  require #SS eq 1: Sprintf("ERROR: number of schemes is %o", #SS);
  
  KK := CoefficientRing(Parent(L));
  ss := SS[1];
  eqns := DefiningEquations(ss);
  R := Parent(eqns[1]);
  a1, a2, a3 := Explode([changebase(MonomialCoefficient(eqns[1],R.i),KK : switch := switch) : i in [1..3]]);
  if #eqns eq 1 then
    if a1 ne 0 then
      M := Matrix(KK,[[a1, -a2, -a3], [0, 1, 0], [0, 0, 1]]);
    else
      M := Matrix(KK,[[1, 0, 0], [0, a2, -a3], [0, 0, 1]]);
    end if;
  end if;
  if #eqns eq 2 then
    b1, b2, b3 := Explode([changebase(MonomialCoefficient(eqns[2],R.i),KK : switch := switch) : i in [1..3]]);
    M := Matrix(KK,[[a1, -a2, -a3], [-b1, b2, -b3], [0, 0, 1]]);
    if b1 eq 0 and b2 eq 0 then
      M := Matrix(KK,[[a1, -a2, -a3], [0, 1, 0], [0, 0, 1]]);
    end if;
  end if;
  return L^M, M;
end intrinsic;


/**************************************************
  HELPER FUNCTION FOR FOWARD SCORING
**************************************************/

// score the complexity of SingularSubschemeModPi(L,pi)
function SingularSubschemeComplexity(L,pi)
  dds := DiagDegrees(L);
  K := Parent(Coefficients(L)[1]);
  perms := StabS3(dds);
  minscore := -1;
  for perm in perms do
    Mp := PermutationMatrix(K,perm);
    Lp := L^Mp;
    try
      SS := SingularSubschemeModPi(Lp, pi);
      ss := SS[1];
      eqns := DefiningEquations(ss);
      R<X,Y,Z> := Parent(eqns[1]);
      score := 0;
      for eqn in eqns do
        coeffs := Coefficients(eqn);
        score := score + Degree(LCM([Denominator(c) : c in coeffs]));
        nY := Numerator(MonomialCoefficient(eqn,Y));
        nZ := Numerator(MonomialCoefficient(eqn,Z));
        if nY eq 0 then
          dY := 0;
        else
          dY := Degree(nY);
        end if;
        if nZ eq 0 then
          dZ := 0;
        else
          dZ := Degree(nZ);
        end if;
        if MonomialCoefficient(eqn,X) ne 0 then
          score := score + Max(2*dY - (dds[2]-dds[1]),0);
          score := score + Max(2*dZ - (dds[3]-dds[1]),0);
        else
          score := score + Max(2*dZ - (dds[3]-dds[2]),0);
        end if;
        if minscore lt 0 or score lt minscore then
          minscore := score;
        end if;
      end for;  
    catch err
      continue;
    end try;
  end for;
  return minscore;
end function;

/**************************************************
  HELPER FUNCTIONS FOR DEGREE MINIMIZATION
**************************************************/

function ReflectPol(c,d,j)
  coeffs, monos := CoefficientsAndMonomials(c);
  n := #coeffs;
  X := Parent(c).1;
  Y := Parent(c).2;
  newc := Parent(c)!0;
  if j eq 1 then
    for i in [1..n] do
      e := Exponents(monos[i]);
      newc := newc + coeffs[i]*X^(d-e[1]-e[2])*Y^(e[2]);
    end for;
  elif j eq 2 then
    for i in [1..n] do
      e := Exponents(monos[i]);
      newc := newc + coeffs[i]*Y^(d-e[1]-e[2])*X^(e[1]);
    end for;
  end if;
  return newc;
end function;

function SwitchAffine(L,j)
  coeffs, monos := CoefficientsAndMonomials(L);
  n := #coeffs;
  d := Maximum([Degree(Numerator(c)) : c in coeffs]);
  newL := Parent(L)!0;
  for i in [1..n] do
    newL := newL + ReflectPol(Numerator(coeffs[i]),d,j)*monos[i];
  end for;
  return newL;
end function;


/**************************************************
  FUNCTIONS TO CARRY OUT MINIMIZATION STEPS
**************************************************/

// We first give two helper functions for degree minimization.
function DegreeMinimization1(L)
  L1 := SwitchAffine(L,1);
  K<g,h> := Parent(Coefficients(L)[1]);
  I3 := IdentityMatrix(K,3);
  pi := g;
  gerr := false;
  L1, Mg1 := Rescale(L1);
  _, polyfact := DiscSqFactors(L1);
  while pi in [fact[1]: fact in polyfact] do
    try
      SS := SingularSubschemeModPi(L1,pi);
    catch err
      gerr := true;
      break;
    end try;
    if SS eq [] then
      gerr := true;
      break;
    end if;
    L2, M2 := TransSingSubscheme(L1, SS : switch := true);
    if IsSing(L2) then
      gerr := true;
      break;
    end if;
    L3, M3 := Rescale(L2);
    if &+(DiagDegrees(L3)) gt &+(DiagDegrees(L1)) then
      gerr := true;
      break;
    end if;
    L1 := L3;  Mg1 := Mg1*M2*M3;
    _, polyfact := DiscSqFactors(L1);
  end while;

  L1 := SwitchAffine(L1,1);
  L1, Mg2 := Rescale(L1);
  _, polyfact := DiscSqFactors(L1);
  while pi in [fact[1] : fact in polyfact] and not gerr do
    try
      SS := SingularSubschemeModPi(L1,pi);
    catch err
      L1 := L;
      Mg1 := IdentityMatrix(K,3);
      Mg2 := IdentityMatrix(K,3);
      break;
    end try;
    if SS eq [] then
      break;
    end if;
    L2, M2 := TransSingSubscheme(L1, SS : switch := true);
    if IsSing(L2) then
      break;
    end if;
    L3, M3 := Rescale(L2);
    if &+(DiagDegrees(L3)) gt &+(DiagDegrees(L1)) then
      break;
    end if;
    L1 := L3;  Mg2 := Mg2*M2*M3;
    _, polyfact := DiscSqFactors(L1);
  end while;
  L0 := L1;

  return L1, Mg1, Mg2, I3, I3;
end function;

function DegreeMinimization2(L)
  L1 := SwitchAffine(L,2);
  K<g,h> := Parent(Coefficients(L)[1]);
  I3 := IdentityMatrix(K,3);
  L1, Mh1 := Rescale(L1);
  _, polyfact := DiscSqFactors(L1);
  pi := h;
  herr := false;
  while pi in [fact[1] : fact in polyfact] do
    try
      SS := SingularSubschemeModPi(L1,pi);
    catch err
      herr := true;
      break;
    end try;
    if SS eq [] then
      herr := true;
      break;
    end if;
    L2, M2 := TransSingSubscheme(L1, SS);
    if IsSing(L2) then
      herr := true;
      break;
    end if;
    L3, M3 := Rescale(L2);
    if &+(DiagDegrees(L3)) gt &+(DiagDegrees(L1)) then
      herr := true;
      break;
    end if;
    L1 := L3;  Mh1 := Mh1*M2*M3;
    _, polyfact := DiscSqFactors(L1);
  end while;

  L1 := SwitchAffine(L1,2);
  L1, Mh2 := Rescale(L1);
  _, polyfact := DiscSqFactors(L1);
  while pi in [fact[1] : fact in polyfact] and not herr do
    try
      SS := SingularSubschemeModPi(L1,pi);
    catch err
      L1 := L;
      Mh1 := IdentityMatrix(K,3);
      Mh2 := IdentityMatrix(K,3);
      break;
    end try;
    if SS eq [] then
      break;
    end if;
    L2, M2 := TransSingSubscheme(L1, SS);
    if IsSing(L2) then
      break;
    end if;
    L3, M3 := Rescale(L2);
    if &+(DiagDegrees(L3)) gt &+(DiagDegrees(L1)) then
      break;
    end if;
    L1 := L3;  Mh2 := Mh2*M2*M3;
    _, polyfact := DiscSqFactors(L1);
  end while;

  return L1, I3, I3, Mh1, Mh2;
end function;


intrinsic DegreeMinimization(L::RngMPolElt) -> RngMPolElt, AlgMatElt, AlgMatElt, AlgMatElt, AlgMatElt
{
  Minimize the conic L at the prime at infinity.
}
  L1 := SwitchAffine(L,1);
  K<g,h> := Parent(Coefficients(L)[1]);
  pi := g;			
  gerr := false;
  L1, Mg1 := Rescale(L1);
  _, polyfact := DiscSqFactors(L1);
  while pi in [fact[1]: fact in polyfact] do
    try
      SS := SingularSubschemeModPi(L1,pi);
    catch err
      gerr := true;
      break;
    end try;
    if SS eq [] then
      gerr := true;
      break;
    end if;
    L2, M2 := TransSingSubscheme(L1, SS : switch := true);
    if IsSing(L2) then
      gerr := true;
      break;
    end if;
    L3, M3 := Rescale(L2);
    if &+(DiagDegrees(L3)) gt &+(DiagDegrees(L1)) then
      gerr := true;
      break;
    end if;
    L1 := L3;  Mg1 := Mg1*M2*M3;
    _, polyfact := DiscSqFactors(L1);
  end while;

  L1 := SwitchAffine(L1,1);
  L1, Mg2 := Rescale(L1);
  _, polyfact := DiscSqFactors(L1);
  while pi in [fact[1] : fact in polyfact] and not gerr do
    try
      SS := SingularSubschemeModPi(L1,pi);
    catch err
      L1 := L;
      Mg1 := IdentityMatrix(K,3);
      Mg2 := IdentityMatrix(K,3);
      break;
    end try;
    if SS eq [] then
      break;
    end if;
    L2, M2 := TransSingSubscheme(L1, SS : switch := true);
    if IsSing(L2) then
      break;
    end if;
    L3, M3 := Rescale(L2);
    if &+(DiagDegrees(L3)) gt &+(DiagDegrees(L1)) then
      break;
    end if;
    L1 := L3;  Mg2 := Mg2*M2*M3;
    _, polyfact := DiscSqFactors(L1);
  end while;
  L0 := L1;

  L1 := SwitchAffine(L1,2);
  L1, Mh1 := Rescale(L1);
  _, polyfact := DiscSqFactors(L1);
  pi := h;
  herr := false;
  while pi in [fact[1] : fact in polyfact] do
    try
      SS := SingularSubschemeModPi(L1,pi);
    catch err
      herr := true;
      break;
    end try;
    if SS eq [] then
      herr := true;
      break;
    end if;
    L2, M2 := TransSingSubscheme(L1, SS);
    if IsSing(L2) then
      herr := true;
      break;
    end if;
    L3, M3 := Rescale(L2);
    if &+(DiagDegrees(L3)) gt &+(DiagDegrees(L1)) then
      herr := true;
      break;
    end if;
    L1 := L3;  Mh1 := Mh1*M2*M3;
    _, polyfact := DiscSqFactors(L1);
  end while;

  L1 := SwitchAffine(L1,2);
  L1, Mh2 := Rescale(L1);
  _, polyfact := DiscSqFactors(L1);
  while pi in [fact[1] : fact in polyfact] and not herr do
    try
      SS := SingularSubschemeModPi(L1,pi);
    catch err
      L1 := L0;
      Mh1 := IdentityMatrix(K,3);
      Mh2 := IdentityMatrix(K,3);
      break;
    end try;
    if SS eq [] then
      break;
    end if;
    L2, M2 := TransSingSubscheme(L1, SS);
    if IsSing(L2) then
      break;
    end if;
    L3, M3 := Rescale(L2);
    if &+(DiagDegrees(L3)) gt &+(DiagDegrees(L1)) then
      break;
    end if;
    L1 := L3;  Mh2 := Mh1*M2*M3;
    _, polyfact := DiscSqFactors(L1);
  end while;

  return L1, Mg1, Mg2, Mh1, Mh2;
end intrinsic;


intrinsic RationalMinimization(L::RngMPolElt) -> RngMPolElt, AlgMatElt
{
Remove rational factors from disc L that can be removed without increasing
diagonal degrees
}
  ratfacts, polyfacts := DiscSqFactors(L);
  ratfacts := Reverse(ratfacts);
  Drat := IntDisc(L);
  L1 := L;
  K := Parent(Coefficients(L)[1]);
  M1 := IdentityMatrix(K,3);
  for fact in ratfacts do
    p := fact[1];
    while true do
      try
        SS := SingularSubschemeModPi(L1,p);
      catch err
        break;
      end try;
      if SS eq [] then
        break;
      end if;
      L2, M2 := TransSingSubscheme(L1, SS);
      if IsSing(L2) then
        break;
      end if;
      L3, M3 := Rescale(L2);
      D3rat := IntDisc(L3);
      if &+(DiagDegrees(L3)) gt &+(DiagDegrees(L1)) or Abs(D3rat) ge Abs(Drat) then
        break;
      end if;
      L1 := L3;  M1 := M1*M2*M3;
      Drat := D3rat;
    end while;
  end for;
  return L1, M1;
end intrinsic;

/**************************************************
  FUNCTIONS TO SCORE NODES AND PATHS
**************************************************/

// compute a degree score for a minimization (lower is better)
// based on degrees of square+ factors of discriminants, diagonal degrees
// and the difference between diagonal degrees and discriminant degreee
function DegScore(L);
  ddsum := &+(DiagDegrees(L));
  discdeg := DiscDegree(L);
  ratfacts, polyfacts := DiscSqFactors(L);
  d := 0;
  for fact in polyfacts do
    d := d + Degree(fact[1])*fact[2];
  end for;
  return d + (ddsum - discdeg);
end function;

// given a list of degree scores, compute the "degree with linear penalty" score
function DegPen1Score(scores)
  n := #scores;
  penalty := 0;			
  count := -1;
  for s in scores do
    if s eq scores[n] then
      count := count + 1;
    end if;
  end for;
  penalty := count;
  return scores[n] + penalty;
end function;

// given a list of degree scores, compute the "degree with square penalty" score
function DegPen2Score(scores)
  n := #scores;
  penalty := 0;			
  count := -1;
  for s in scores do
    if s eq scores[n] then
      count := count + 1;
    end if;
  end for;
  penalty := (0.5*count)^2;
  return scores[n] + penalty;
end function;

// given a list of degree scores, compute the average slope score
function SlopeScore(scores)
  n := #scores;
  return 1.0*(scores[n]-scores[1])/n;
end function;

function PathScore(scores : method:="slope")
  case method:
    when "deg1":
      return DegPen1Score(scores);
    when "deg2":
      return DegPen2Score(scores);
    when "alt":
      if #scores mod 2 eq 1 then
        return SlopeScore(scores);
      else
        return DegPen2Score(scores);
      end if;
    else:
      return SlopeScore(scores);
  end case;
end function;

function NodeScore(L : fwd:=false)
  score := DegScore(L);
  ratfacts, polfacts := DiscSqFactors(L);
  score := score + #ratfacts;
  if fwd then
    for fact in ratfacts do
      pi := fact[1];
      if pi gt 2 then
        s := SingularSubschemeComplexity(L,pi);
        if s ge 0 then
          score := score + s; 
        end if;
      end if;
    end for;
    for fact in polfacts do
      pi := fact[1];
      if Degree(pi) le 4 then
        s := SingularSubschemeComplexity(L,pi);
        if s ge 0 then
          score := score + s - Degree(pi);
        end if;
      end if;
    end for;
  end if;
  return score;
end function;


/**************************************************
  FUNCTIONS TO CARRY OUT MINIMIZATION STEPS IN ALGORITHM
**************************************************/

intrinsic RationalAndDegreeMinimization(branch::Any : fwd:=false) -> Any, BoolElt
{
Apply degree minimization and rational minimization concurrently. This function 
looks for rational factor and degree minimizations for all good re-orderings 
}
//this is Minimization Step A in the MinimizationSearch function
  L := branch`pol;
  K := Parent(Coefficients(L)[1]);
  M := IdentityMatrix(K,3);
  Drat := IntDisc(L);
  
  reducedrat := false;
  L0 := L;
  for perm in StabS3(DiagDegrees(L0)) do                                      // do best rat minimization
    Mp := PermutationMatrix(K,perm);                                          // for re-orderings
    Lp := (branch`pol)^Mp;
    L1, M1 := RationalMinimization(Lp);
    D1rat := IntDisc(L);
    if Abs(D1rat) lt Abs(Drat) then
      L := L1;  M := Mp*M1;
      reducedrat := true;
    end if;
  end for;
  newtrans := [];
  if reducedrat then
    newtrans := [[M]];
  end if;

  L0 := L;
  degsum := &+(DiagDegrees(L0));
  reduceddegree := false;
  M0 := IdentityMatrix(K,3);
  for perm in StabS3(DiagDegrees(L0)) do                                      // do best deg minimization
    Mp := PermutationMatrix(K,perm);                                          //   for re-orderings
    Lp := L0^Mp;  
    L1, Mg1, Mg2, Mh1, Mh2 := DegreeMinimization1(Lp);
    if &+(DiagDegrees(L1)) lt degsum then
      L := L1; Ms := [Mg1, Mg2, Mh1, Mh2];  M0 := Mp;
      degsum := &+(DiagDegrees(L1));
      reduceddegree := true;
    end if;
    L2, Mg1, Mg2, Mh1, Mh2 := DegreeMinimization2(Lp);
    if &+(DiagDegrees(L2)) lt degsum then
      L := L2; Ms := [Mg1, Mg2, Mh1, Mh2];  M0 := Mp;
      reduceddegree := true;
    end if;
  end for;
  if reduceddegree then
    if M0 ne 1 then
      Append(~newtrans,[M0]);
    end if;
    Append(~newtrans, Ms);
  end if;

  if reducedrat or reduceddegree then
    nn := rec< Node | pol := L>; 
    nn`scores := Append(branch`scores, NodeScore(L : fwd := fwd));
    nn`trans := branch`trans cat newtrans;
    return [nn], true;
  end if;

  return [branch], false;
end intrinsic;


intrinsic PolynomialMinimization(branch::Any : fwd := false) -> Any
{
Compute branches in the minimization search tree which arise from minimizing at polynomial factors
of the discriminant of the branch.
}
// this is Minimization Step B in MinimizationSearch algorithm
  nodes := [];
  L0 := branch`pol;
  P2<x0,x1,x2> := Proj(Parent(L0));
  D := Numerator(Discriminant(Conic(P2, L0)));
  KK<g,h> := Parent(D);
  K := Parent(Coefficients(L0)[1]);
  facts := Factorization(D);
  for fact in facts do                                                        //   for re-orderings
    pi := fact[1];
    swap := IsUnivariate(pi,g);

    L := L0;
    transformed := false;
    for perm in StabS3(DiagDegrees(L0)) do
      Mp := PermutationMatrix(K,perm);		
      Lp := L0^Mp;
      try
        L1, M1 := TransSingSubscheme(Lp,SingularSubschemeModPi(Lp,pi) : switch:=swap);
	      L2, M2 := Rescale(L1);
        if DegScore(L2) le DegScore(L0) then
          transformed := true;
          L := L2;  M := Mp*M1*M2;
        end if;
      catch err
        e := 1;
      end try;  
    end for;

    if transformed then
      nn := rec< Node | pol:=L>;
      nn`scores := Append(branch`scores, NodeScore(L : fwd:=fwd));
      nn`trans := Append(branch`trans, [M]);
      Append(~nodes, nn);
    end if;
  end for;

  return nodes;
end intrinsic;


/**************************************************
  Inspection procedure (for verbose printing)
**************************************************/

procedure inspect(L)
  R := Parent(Coefficients(L)[1]);
  P2<x0,x1,x2> := Proj(Parent(L));
  diagmons := [x0^2, x1^2, x2^2];
  mcs := [MonomialCoefficient(L,m) : m in diagmons];
  printf "Degrees of numerators of diagonal coefficients: %o\n", [Degree(Numerator(c)) : c in mcs];
  printf "Degrees of denominators of diagonal coefficients: %o\n", [Degree(Denominator(c)) : c in mcs];
  D := Discriminant(Conic(P2, L));
  D := Numerator(D)*Denominator(D);
  D := D*(LCM([Denominator(c) : c in Coefficients(D)]));
  D := PolynomialRing(ZZ, 2)!D;
  printf "The discriminant factors as:\n%o\n", [<Evaluate(d[1], [R.1, R.2]), d[2]> : d in FactNum(D)];
end procedure;


/**************************************************
  THE MAIN ALGORITHM
**************************************************/

/*  
The steps of the algorithm are as follows:
A. 1) remove rational factors from disc without increasing diag degrees, and
   2) do degree minimization by minimizing at infinity; OR
B. create a branch for each poly π with π^2 | disc of minimization wrt π
   we do (B) if (A) does not result in any minimization.
*/

intrinsic MinimizationSearch(L::RngMPolElt : maxsteps:=100, method:="slope", randomization:=false) -> Any
{
Do a search for best minimizations of Mestre conic L. 
INPUTS: A conic L defined over a two variable function field ℚ(t1,t2). 
OUTPUS: A node (or list of nodes if the search fails) corresponding to a minimized conic (resp. all nodes 
in the search tree).
}

  case method:
    when "deg1":
      scorename := "degree score with linear penalty";
    when "deg2":
      scorename := "degree score with square penalty";
    when "alt":
      scorename := "alternating score between avg and deg2";
    when "fwd":
      scorename := "forward-looking score";
    when "forward":
      scorename := "forward-looking score";
    else:
      scorename := "average slope score";
  end case;

  ////////////////////
  // Verbose printing
  vprint ConicMinimize, 1: "|" cat &cat["-" : i in [1..75]] cat "|";
  vprint ConicMinimize, 1: "|" cat &cat[" " : i in [1..75]] cat "|";
  vprintf ConicMinimize, 1: "| %-73o |\n", "Minimization process begin run with the following flags set";
  vprintf ConicMinimize, 1: "| %o %-54o |\n", "Path score method:", scorename;
  vprintf ConicMinimize, 1: "| %o %-53o |\n", "Randomization flag:", randomization;
  vprint ConicMinimize, 1: "|" cat &cat[" " : i in [1..75]] cat "|";
  vprint ConicMinimize, 1: "|" cat &cat["-" : i in [1..75]] cat "|\n";

  if IsVerbose("ConicMinimize", 2) then
    inspect(L);
  end if;
  ////////////////////
  
  if method in ["fwd", "forward"] then
    fwd := true;
    method := "deg2";
  else
    fwd := false;
  end if;
  
  nsteps := 1;
  L1, M1 := Rescale(L);
  nodes := [rec< Node | pol := L1, scores := [NodeScore(L1 : fwd := fwd)], trans := [[M1]]>];
  visited := [L1];

  while nsteps le maxsteps do                                                 // nodes = leaves of search
    n := #nodes;                                                              //         tree
    minscore := PathScore(nodes[1]`scores : method := method);
    mini := 1;

    for i in [2..n] do                                                        // find node with min score
      m := PathScore(nodes[i]`scores : method := method);
      if m lt minscore then
        mini := i;
	      minscore := m;
      end if;
    end for;
    oldnodes := [];

    if randomization then
      if Random(8) eq 0 then                                                  // random branch with prob 1/8
        mini := 1 + Random(n-1);
      end if;
    end if;

    branch := nodes[mini];                                                    // branch tree at this node

    ////////////////////
    // Verbose printing
    vprint ConicMinimize, 2: "\n" cat &cat["-" : i in [1..47]];
    vprintf ConicMinimize, 2: "| %o Step %o %o|\n", &cat[" " : i in [1..16]], nsteps, &cat[" " : i in [1..21-#Sprint(nsteps)]];
    vprint ConicMinimize, 2: &cat["-" : i in [1..47]];
    vprintf ConicMinimize, 2: "| %-20o | %-20o |\n", "Depth", #branch`scores;
    vprintf ConicMinimize, 2: "| %-20o | %-20.4o |\n", "Branch", minscore;
    vprintf ConicMinimize, 2: "| %-20o | %-20o |\n", "Discriminant degree", DiscDegree(branch`pol);
    vprintf ConicMinimize, 2: "| %-20o | %-20o |\n", "Diagonal degrees", DiagDegrees(branch`pol);
    vprint ConicMinimize, 2: &cat["-" : i in [1..47]];
    ////////////////////
    
    newnodes0, reduced := RationalAndDegreeMinimization(branch : fwd := fwd); // try Red Step A
    if not reduced then			
      newnodes0 := PolynomialMinimization(branch : fwd := fwd);               // if not try Red Step B
    end if;


    if reduced then
      Lpol := newnodes0[1]`pol;
      vprint ConicMinimize, 2: "We're now minimizing at rational primes and infty"; 
    else
      vprint ConicMinimize, 2: "We're now minimizing at polynomial factors of the discriminant";
    end if;

    newnodes := [];				
    for nn in newnodes0 do			
      Lpol := nn`pol;                                                         // if a new node has score 0
      if DegScore(Lpol) eq 0 then                                             //	return this
        vprint ConicMinimize, 1: "\n\nSEARCH SUCCEEDED: minimal form found!\n";
        final := DiagonalizeNode(nn);
        vprint ConicMinimize, 1: final`pol;
        return final;
      end if;
                                                                              // only add unseen nodes
      if not(Lpol in visited) and not(-Lpol in visited) then 
        vprint ConicMinimize, 2: "We have a new node with:";
        vprintf ConicMinimize, 2: "  --Discriminant degree %o, and\n", DiscDegree(Lpol);
        vprintf ConicMinimize, 2: "  --Diagonal degrees %o\n", DiagDegrees(Lpol);
        Append(~visited, Lpol);
        Append(~newnodes, nn);
      end if;
    end for;

    for i in [1..n] do                                                        // update list of nodes
      if i ne mini then                                                       // using new branch
        Append(~oldnodes, nodes[i]);
      end if;
    end for;
    nodes := oldnodes cat newnodes;

    if #nodes eq 0 then
      print "\n\nSEARCH FAILED: all admissible paths tried\n";
      return nodes;
    end if;
    nsteps := nsteps + 1;

  end while;

  vprintf ConicMinimize, 1: "\n\nSEARCH FAILED: we exceeded the maximum number of steps (set to %o)", maxsteps;
  
  return nodes;                                                               
end intrinsic;


intrinsic MinimizationSearch(L::CrvCon : maxsteps:=100, method:="slope", randomization:=false) -> Any
{
Do a search for best minimizations of Mestre conic L
INPUTS:
OUTPUS:

The steps are as follows:
A. 1) remove rational factors from disc without increasing diag degrees, and
   2) do degree minimization by minimizing at infinity; OR
B. create a branch for each poly π with π^2 | disc of minimization wrt π
   we do (B) if (A) does not result in any minimization.
}
  LL := DefiningPolynomial(L);
  return MinimizationSearch(LL : maxsteps:=maxsteps, method:=method, randomization:=randomization);
end intrinsic;

/**************************************************
  ApplyTrans 
**************************************************/

intrinsic ApplyTrans(L0::RngMPolElt, trans::SeqEnum) -> Any
{
Apply the transformation (in the format returned by MinimizationSeach)
to the conic L0.
INPUTS: Conic L0 and transformation trans (as returned by MinimizationSearch)
OUTPUTS: Conic L = L0^M
}
  L := L0 * LCM([Denominator(c) : c in Coefficients(L0)]);
  for M in trans do
    if #M eq 1 then
      L := L^M[1];
      L := L * LCM([Denominator(c) : c in Coefficients(L)]);
    elif #M eq 4 then
      L := SwitchAffine(L, 1); L := L^M[1];
      L := L * LCM([Denominator(c) : c in Coefficients(L)]);
      L := SwitchAffine(L, 1); L := L^M[2];
      L := L * LCM([Denominator(c) : c in Coefficients(L)]);
      L := SwitchAffine(L, 2); L := L^M[3];
      L := L * LCM([Denominator(c) : c in Coefficients(L)]);
      L := SwitchAffine(L, 2); L := L^M[4];
      L := L * LCM([Denominator(c) : c in Coefficients(L)]);
    end if;
  end for;
  return L;
end intrinsic;


intrinsic ApplyTrans(L0::CrvCon, trans::SeqEnum) -> Any
{
Apply the transformation (in the format returned by MinimizationSeach)
to the conic L0.
INPUTS: Conic L0 and transformation trans (as returned by MinimizationSearch)
OUTPUTS: Conic L = L0^M
}
  LL := DefiningPolynomial(L0);
  P2 := AmbientSpace(L0);
  L := ApplyTrans(LL, trans);
  return Conic(P2, L);
end intrinsic;
