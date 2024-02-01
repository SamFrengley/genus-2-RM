AttachSpec("../minimize/spec");
AttachSpec("../models/spec");

function MakeHMSFunctionField(D, K)
  // Makes the function field ℚ(g,h)[z]/(z^2 - λ_D)
  PP<z> := PolynomialRing(K);
  lambda_D := Getlambda_D(D : coords:=[K.1, K.2]);
  return quo<PP | z^2 - lambda_D>;
end function;

"==================================================";
"PROOF OF THEOREM 1.5: q_D CASE";
"==================================================";

QQ := Rationals();
K<g,h> := FunctionField(QQ, 2);

DISCRIMINANTS := [5, 8, 12, 13, 17, 21, 24, 28, 29, 33, 37, 44, 53, 61];

for D in DISCRIMINANTS do
  print "\n----------------------------------------";
  
  if D eq 17 then
    print "Not implemented: Proof of q_D=1 for \ndiscriminant 17 follows from p_D case \n(1 is a function on the Humbert surface)";
      
  else
    printf "Proof of q_D for discriminant %o\n", D;  
    phi, phi_inv := eval Read("coord-change/" cat Sprint(D) cat ".m");

    if D eq 33 then
      ICinvs := GetIgusaClebschInvariants(D : vars:=phi);
      L,M := ICConicCubic(ICinvs);
    else
      RMinvs := GetRMInvariants(D : vars:=phi);
      L,M := RMConicCubic(RMinvs);
    end if;    

    // Get the requisite transformations
    //    trans := "humb-trans/" cat Sprint(D) cat ".m";
    trans := "trans/" cat Sprint(D) cat "/trans_humb.m";
    trans := eval Read(trans);
    trans := [[Matrix(K, 3, 3, A) : A in AA] : AA in trans];

    // Apply the transformations
    L := ApplyTrans(L, trans);
    L := EvaluateCoefficients(L, phi_inv);
    L := ClearDens(L);
    M := ApplyTrans(M, trans);
    M := EvaluateCoefficients(M, phi_inv);
    M := ClearDens(M);

    // Make a final transformation on the HMS
    KK<z> := MakeHMSFunctionField(D, K);
    P2<X,Y,Z> := PolynomialRing(KK, 3);

    // Coerce into function field of HMS
    L := P2!L; M := P2!M;

    // Get the transformations
    trans := "trans/" cat Sprint(D) cat "/trans_hms.m";
    trans := eval Read(trans);
    trans := [Matrix(KK, 3, 3, A) : A in trans];

    // Apply the transformations
    for A in trans do
      L := L^A;
      M := M^A;
    end for;

    ////////////
    // The proof 
    L_test := P2!GetTransformedMestreConic(D : coords:=[g,h]);
    flag := IsDivisibleBy(L, L_test);
    printf "The conic part is %o\n", flag;
    assert IsDivisibleBy(L_test, L); //degrees are the same, so should be OK

    M_test := P2!GetTransformedMestreCubic(D : coords:=[g,h,z]);
    flag := IsDivisibleBy(M, M_test);
    printf "The cubic part is %o\n", flag;
    assert IsDivisibleBy(M_test, M); //degrees are the same, so should be OK
  end if;
end for;
