AttachSpec("../models/spec");

"==================================================";
"PROOF OF THE 3-FOLD PARAMETRISATIONS BEING BIRATIONAL";
"==================================================";

print "We prove that the stored birational trasformations are indeed birational";
print "Note that we do not check D=17 since in that case we only store a section\n";
DISCS_rat := [8, 12, 13];

print "=========================";
print "First the rational cases.\n";

for D in DISCS_rat do
  print "------------------";
  printf "The case when D=%o\n\n", D;
  
  A4<m,n,r,s> := AffineSpace(Rationals(), 4);
  A3<a,b,c> := AffineSpace(Rationals(), 3);
  p_D := Getp_D(D : coords:=[m,n]);

  scrL := r^2 - D*s^2 - p_D;
  scrL := Scheme(A4, scrL);
  
  param := eval Read("3fold-param/" cat Sprint(D) cat ".m");
  param := map<A3 -> scrL | param>;
  assert IsInvertible(param);
end for;

print "=======================================";
print "Now the non-rational cases except D=24.\n";
DISCS_nonrat := [21, 28, 29, 37, 44, 53, 61];

for D in DISCS_nonrat do
  print "------------------";
  printf "The case when D=%o\n\n", D;
  
  A4<g,h,r,s> := AffineSpace(Rationals(), 4);
  A3<a,b,c> := AffineSpace(Rationals(), 3);
  q_D := Getq_D(D : coords:=[g,h]);

  scrL := r^2 - D*s^2 - q_D;
  scrL := Scheme(A4, scrL);
  
  param := eval Read("3fold-param_LDH/" cat Sprint(D) cat ".m");
  param := map<A3 -> scrL | param>;
  assert IsInvertible(param);
end for;

print "=======================================";
print "Finally D=24 which is over Q(sqrt(-2)).\n";

for D in [24] do
  print "------------------";
  printf "The case when D=%o\n\n", D;
  Q<sqrt_2> := QuadraticField(-2);
  A4<g,h,r,s> := AffineSpace(Q, 4);
  A3<a,b,c> := AffineSpace(Q, 3);
  q_D := Getq_D(D : coords:=[g,h]);

  scrL := r^2 - D*s^2 - q_D;
  scrL := Scheme(A4, scrL);
  
  param := eval Read("3fold-param_LDH/" cat Sprint(D) cat ".m");
  param := map<A3 -> scrL | param>;
  assert IsInvertible(param);
end for;
