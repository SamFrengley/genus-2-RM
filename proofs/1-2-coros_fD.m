AttachSpec("../models/spec");

"==================================================";
"PROOF OF Corollaries 1.2, 1.3, 7.1, 7.2";
"==================================================";

DISCRIMINANTS := [8, 12, 13, 17];

for D in DISCRIMINANTS do
  if D eq 17 then 
    KK<a,b> := FunctionField(Rationals(), 2);
  else
    KK<a,b,c> := FunctionField(Rationals(), 3);
  end if;
  
  P<x> := PolynomialRing(KK);

  // If D = 17 this is not a parametrisation, just a change
  // of coords with a chosen section.
  m,n,r,s := Explode(eval Read("3fold-param/" cat Sprint(D) cat ".m"));
  
  L := GetTransformedMestreConic(D : coords:=[m,n], rat:=true);
  M := GetTransformedMestreCubic(D : coords:=[m,n], rat:=true);
  assert Evaluate(L, [r,s,1]) eq 0; //check we have a point

  // Parametrise the conic and substitute into the cubic
  r_para, s_para, den := Explode(eval Read("conic-param_abc/" cat Sprint(D) cat ".txt"));
  r_para := r_para/den;
  s_para := s_para/den;
  
  assert Evaluate(L, [r_para,s_para,1]) eq 0;
  f := Evaluate(M, [r_para,s_para,1]);

  if D eq 17 then
    f_test := RMWeierstrassEquationRational(D, [a,b]);
  else
    f_test := RMWeierstrassEquationRational(D, [a,b,c]);
  end if;
  
  flag := IsDivisibleBy(f, f_test);
  printf "The proof is %o for discriminant %o\n", flag, D;
end for;
