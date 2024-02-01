AttachSpec("../minimize/spec");
AttachSpec("../models/spec");

function MakeHMSFunctionField(D, K)
  // Makes the function field ℚ(g,h)[z]/(z^2 - λ_D)
  PP<z> := PolynomialRing(K);
  lambda_D := Getlambda_D(D : coords:=[K.1, K.2]);
  return quo<PP | z^2 - lambda_D>;
end function;

"==================================================";
"PROOF OF THEOREM 1.1";
"==================================================";

print "At this point, you should have run thm-1-5.m to convince yourself";
print "that the stored cubic are correct. Granting that, here is the proof";
print "of Theorem 1.1:\n\n";

QQ := Rationals();
K<g,h> := FunctionField(QQ, 2);

DISCRIMINANTS := [5, 8, 12, 13, 17, 21, 24, 28, 29, 33, 37, 44, 53, 61];
for D in [d : d in DISCRIMINANTS] do
  print "\n----------------------------------------";
  printf "Proof for discriminant %o\n", D;
  K<g,h> := FunctionField(QQ, 2);
  KK<z> := MakeHMSFunctionField(D, K);
  P2<X,Y,Z> := PolynomialRing(KK, 3);
  
  // Get the conic and cubic
  L := P2!GetTransformedMestreConic(D : coords:=[g,h]);
  M := P2!GetTransformedMestreCubic(D : coords:=[g,h,z]);

  L := Curve(Proj(P2), L);  
  K_scrL<r,s> := FunctionField(L);
  _<x> := PolynomialRing(K_scrL);
  
  param := eval Read("conic-param/" cat Sprint(D) cat ".txt");
  assert Evaluate(DefiningPolynomial(L), param) eq 0;
  
  F_D := Evaluate(M, param);

  flag := IsDivisibleBy(RMWeierstrassEquation(D, z,g,h,r,s), F_D);
  printf "The proof was %o\n", flag;
end for;

