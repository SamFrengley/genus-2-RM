AttachSpec("../models/spec");

function MakeHMSFunctionField_ish(D, K)
  // Makes the function field ℚ(a,b,c)[z]/(z^2 - Λ_D)
  PP<z> := PolynomialRing(K);
  Lambda_D := GetUpperLambda_D(D : coords:=[K.1, K.2, K.3]);
  return quo<PP | z^2 - Lambda_D>;
end function;

"==================================================";
"PROOF OF THE POLYNOMIALS f IN THE NON-RATIONAL CASE";
"==================================================";

print "At this point, you should have run thm-1-1.m to convince yourself";
print "that the stored F are correct. Granting that, here is the proof";

QQ := Rationals();
DISCRIMINANTS := [21, 28, 29, 37, 44, 53, 61];

for D in DISCRIMINANTS do
  print "\n----------------------------------------";
  printf "Proof for discriminant %o\n", D;
  K<a,b,c> := FunctionField(QQ, 3);
  KK<zeta> := MakeHMSFunctionField_ish(D, K);
  P2<X,Y,Z> := PolynomialRing(KK, 3);
  
  g,h,r,s := Explode(eval Read("3fold-param_LDH/" cat Sprint(D) cat ".m"));

  _, correction := IsSquare(Getlambda_D(D : coords:=[g,h])/GetUpperLambda_D(D : coords:=[a,b,c]));
  z := correction*zeta;

  F := RMWeierstrassEquationLambda(D, zeta, a, b, c);
  F_test := RMWeierstrassEquation(D, z, g, h, r, s); 

  KK<a,b,c,zeta> := FunctionField(QQ, 4);
  _<x> := PolynomialRing(KK);
  // Testing divisibility in the function field with the relation takes
  // ages, so just test it here.
  F := eval Sprint(F);
  F_test := eval Sprint(F_test);

  assert IsDivisibleBy(F, F_test);  
end for;
