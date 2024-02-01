/**************************************************
Sanity checking the equations F_D(z,u,v,r,s; x);
**************************************************/

AttachSpec("../models/spec");
CC := ComplexField(500);
PP<x> := PolynomialRing(CC);

DISCRIMINANTS := [5, 8, 12, 13, 21, 24, 28, 29, 33, 37, 44, 53, 61];

print "====================================";
print "FIRST TEST: Points which should lift";
print "====================================";
// Pairs of a discriminant and a point on H_D lifting to Y_(D)
tests := [
  //  <5, GetHMSParam(5 : coords:=[3,4])>,
  <8, GetHMSParam(8 : coords:=[3,4])>,
  <12, GetHMSParam(12 : coords:=[3,4])>,
  //  <13, GetHMSParam(13 : coords:=[3,4])>,
  <17, GetHMSParam(17 : coords:=[3,4])>,
  <21, [3/2,1/44]>,
  <24, [1,3/2]>,
  <28, [7/3, -11/3]>,
  <29, [40,-40]>,
  <37, [7/2,3]>,
  <44, [-2,-7/6]>,
  <53, [16/63, -5]>,
  <61, [-3/2,1/2]>
];

for t in tests do
  f := RMWeierstrassEquation(t[1], t[2][1], t[2][2] : extend_base:=false);
  A := AnalyticJacobian(PP!f);
  E := EndomorphismAlgebra(A);
  
  min_plys := [MinimalPolynomial(g) : g in Generators(E)];
  flag := exists{m : m in min_plys | Discriminant(m) eq t[1]};
  printf "The first test for D=%o is %o\n", t[1], flag;
end for;


print "\n=============================================";
print "SECOND TEST: Random points on Humbert surface";
print "=============================================";
// Take points on H_D and lift them arbitrarily and check end alg

for D in DISCRIMINANTS do
  g,h := Explode([Random(-100, 100)/Random(1, 50) : i in [1..2]]);

  r := CC!0;
  conic := GetTransformedMestreConic(D : coords:=[g,h]);
  s := Roots(Evaluate(conic, [r,x,1]))[1][1];
  
  lambda := Getlambda_D(D : coords:=[g,h]);
  z := Roots(x^2 - lambda)[1][1];
  
  f := RMWeierstrassEquation(D, z,g,h,r,s);
  A := AnalyticJacobian(PP!f);
  E := EndomorphismAlgebra(A);

  min_plys := [MinimalPolynomial(g) : g in Generators(E)];
  flag := exists{m : m in min_plys | Discriminant(m) eq D};
  printf "The second test for D=%o is %o\n", D, flag;
end for;
