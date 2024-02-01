AttachSpec("../minimize/spec");
AttachSpec("../models/spec");

"==================================================";
"PROOF OF THEOREM 1.5: p_D CASE";
"==================================================";

QQ := Rationals();
K<g,h> := FunctionField(QQ, 2);
P2<X,Y,Z> := PolynomialRing(K, 3);

RATIONAL_DISCRIMINANTS := [8, 12, 13, 17];
// RATIONAL_DISCRIMINANTS := [13];

for D in RATIONAL_DISCRIMINANTS do
  print "\n----------------------------------------";
  printf "Proof of p_D for discriminant %o\n", D;

  ICinvs := GetIgusaClebschInvariants(D : coords:=[g,h]);
  L,M := MestreConicCubic(ICinvs);
              
  L := P2!L; M := P2!M;
  
  // Get the requisite Humbert transformations
  trans := "trans_rat/" cat Sprint(D) cat "/trans_humb.m";
  trans := eval Read(trans);
  trans := [[Matrix(K, 3, 3, A) : A in AA] : AA in trans];

  // Apply the transformations
  L := ApplyTrans(L, trans);
  L := ClearDens(L);
  M := ApplyTrans(M, trans);
  M := ClearDens(M);

  // Coords on the HMS
  m := g; n := h;
  param := GetHMSParam(D : coords:=[m,n]);
  L := EvaluateCoefficients(L, param);
  M := EvaluateCoefficients(M, param);
  
  // Get the requisite HMS transformations
  trans := "trans_rat/" cat Sprint(D) cat "/trans_hms.m";
  trans := eval Read(trans);
  trans := [[Matrix(K, 3, 3, A) : A in AA] : AA in trans];

  // Apply the transformations
  L := ApplyTrans(L, trans);
  L := ClearDens(L);
  M := ApplyTrans(M, trans);
  M := ClearDens(M);

  /////////////////
  // Checks
  L_test := P2!GetTransformedMestreConic(D : coords:=[m,n], rat:=true);
  flag := IsDivisibleBy(L, L_test);
  printf "The conic part is %o\n", flag;

  M_test := P2!GetTransformedMestreCubic(D : coords:=[m,n], rat:=true);
  flag := IsDivisibleBy(M, M_test);
  printf "The cubic part is %o\n", flag;
  assert IsDivisibleBy(M_test, M); //degrees are the same, so should be OK

end for;


D := 17;
print "\n----------------------------------------";
print "Finally, recall that we outsourced the proof";
printf "of the polynomial F_%o to this file when we\n", D;
printf "have discriminant %o\n\n", D;

// This proof uses the computation of the polynomial p_D for D=17 and the analogously
// transformed Mestre cubic
KK<m,n> := FunctionField(Rationals(), 2);
M := GetTransformedMestreCubic(D : coords:=[m,n], rat:=true); // this is proved above

A2 := AffineSpace(Rationals(), 2);
Y<g,h,z> := AffineSpace(Rationals(), 3);
Y := Surface(Y, z^2 - Getlambda_D(17 : coords:=[g,h]));

map := GetHMSParam(17 : coords:=[A2.1, A2.2]);
_, map3 := IsSquare(Getlambda_D(17 : coords:=map));
map := map cat [map3];

hard_code_inverse := [
  -1*(8*g - 27*h + 4)/((2*g + 1)^(1)*(27*g + 13)),
  -1*(3)^(4)*(22*g^2 + 21*g + 2*h - 2*z + 5)/((2*g + 1)^(2)*(27*g + 13))
];

// Define a birational map between A^2 and Y_(17). Check that the inverse
// we provide really is an inverse, too
phi := map<A2 -> Y | map, hard_code_inverse : CheckInverse:=true>;

KK<g,h> := FunctionField(Rationals(), 2);
KK<z> := PolynomialRing(KK);
KK<z> := quo<KK | z^2 - Getlambda_D(17 : coords:=[g,h])>;
PP<X,Y,Z> := PolynomialRing(KK, 3);

pp := [Evaluate(p, [g,h,z]) : p in hard_code_inverse];
cc,ms := CoefficientsAndMonomials(M);
cc := [Evaluate(c, pp) : c in cc];
ms := [Monomial(PP, Exponents(m)) : m in ms];
M := &+[ms[i]*cc[i] : i in [1..#ms]];

M_test := PP!GetTransformedMestreCubic(D : coords:=[g,h,z]);
flag := IsDivisibleBy(M, M_test);

printf "The proof of the cubic in (z,g,h) is %o when D=17", flag;
assert IsDivisibleBy(M_test, M); //same degree, should hold

