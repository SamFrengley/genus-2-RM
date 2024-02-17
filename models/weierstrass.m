CURR_DIR := "THIS/NEEDS/TO/CONTAIN/THE/PATH/ENDING/AT/models";

intrinsic RMQuadraticOverAlgebra(D::RngIntElt, abc::SeqEnum) -> RngUPolElt, RngUPolElt
{
  Return the quadratic polynomial q(x) ∈ L[x] where L/k is a cubic algebra.
}
  require D mod 4 eq 0: "D should be 0 mod 4";
  require D in [8, 12]: "D should be either 8 or 12";
  abc := [FieldOfFractions(abc[1]) | aa : aa in abc];

  return Get_xi_phi(D : coords:=abc);
end intrinsic;


intrinsic RMWeierstrassEquationRational(D::RngIntElt, abc::SeqEnum) -> RngUPolElt
{
  Return the Weierstrass equation of the genus 2 curve C: y^2 = f(a,b,c;x) with 
  RM D given by the parameters a,b,c.
}
  require D in [5,8,12,13,17]: "D should be <= 17";
  if D eq 17 then
    require #abc eq 2: "abc should have length 2 when D = 17";
  else
    require #abc eq 3: "abc should have length 3 when D is not 17";
  end if;

  k := FieldOfFractions(Parent(abc[1]));
  if #abc eq 2 then
    a,b := Explode([k | a : a in abc]);
  else
    a,b,c := Explode([k | a : a in abc]);
  end if;
  
  P<x> := PolynomialRing(k);

  f_file := CURR_DIR cat "f_abc/" cat Sprint(D) cat ".txt";
  f := eval Read(f_file);
  
  return f;
end intrinsic;


intrinsic RMWeierstrassEquation(D::RngIntElt, g::RngElt, h::RngElt : extend_base:=false) -> RngUPolElt
{
  Given coordinates g,h on the Humbert surface, return the Weierstrass equation 
  of a genus 2 curve RM D corresponding to that point. Unless extend_base:=true the
  field will not be extended.
}
  require D in [5,8,12,13,17,21,24,28,29,33,37,44,53,61]: "D is not in our little database";
  gh := [g,h];
  g,h := Explode(gh);
  k := FieldOfFractions(Parent(g));
  lambda := Getlambda_D(D : coords:=[g,h]);
  flag := IsSquare(lambda);
  if flag then
    L := k;
    _,z := IsSquare(lambda);
  elif extend_base then
    P<z> := PolynomialRing(k);
    L<z> := quo<P | z^2 - lambda>;
  else
    require false: "λ_D(g,h) is not a square in the base field, maybe set extend_base:=true";
  end if;

  P2<X,Y,Z> := ProjectiveSpace(L, 2);
  C := GetTransformedMestreConic(D : coords:=[g,h,z]);
  C := Conic(P2, C);
  try
    flag := HasRationalPoint(C);
    if flag then
      K := L;
      P := RationalPoint(C);
    elif extend_base then
      P<sqrt_D> := PolynomialRing(L);
      K<sqrt_D> := quo<P | sqrt_D^2 - D>;
      P := RationalPoint(BaseChange(C, K));
    else
      require false: "p_D is not a norm, maybe set extend_base:=true";
    end if;
  catch e
    e;
    require false: "You should supply data making p_D a norm";
  end try;

  u,v,w := Explode(Coordinates(P));
  r := u/w; s := v/w;
  
  F := RMWeierstrassEquation(D, z,g,h,r,s);
  
  return F;
end intrinsic;


intrinsic RMWeierstrassEquation(D::RngIntElt, z::RngElt, g::RngElt, h::RngElt, r::RngElt, s::RngElt) -> RngUPolElt
{
  Given coordinates z,g,h on the Humbert surface, return the Weierstrass equation 
  of a genus 2 curve RM D corresponding to that point. 
}
  g,h,z,r,s := Explode([g,h,z,r,s]);
  lambda := Getlambda_D(D : coords:=[g,h]);
  
  if Type(Parent(z)) cmpeq FldCom then
    assert Modulus(z^2 - lambda) lt 10^(-10);
  else
    assert z^2 eq lambda;
  end if;

  q := Getq_D(D : coords:=[g,h]);

  if Type(Parent(z)) cmpeq FldCom then
    assert Modulus(r^2 - D*s^2 - q) lt 10^(-10);
  else
    assert r^2 - D*s^2 eq q;
  end if;
  
  _<x> := PolynomialRing(Parent(g));
  F_file := CURR_DIR cat "F_zghrs/" cat Sprint(D) cat ".txt";
  F := eval Read(F_file);
  return F;
end intrinsic;


intrinsic RMWeierstrassEquationLambda(D::RngIntElt, zeta::RngElt, a::RngElt, b::RngElt, c::RngElt) -> RngUPolElt
{
  Given coordinates zeta,a,b,c such that zeta^2 = Λ , return the Weierstrass equation 
  of a genus 2 curve RM D corresponding to that point. 
}
  require D in [21,28,29,37,44,53,61]: "We do not know of this model for such D";

  if Type(Parent(zeta)) cmpeq FldCom then
    assert Modulus(zeta^2 - GetUpperLambda_D(D : coords:=[a,b,c])) lt 10^(-10);
  else
    assert zeta^2 eq GetUpperLambda_D(D : coords:=[a,b,c]);
  end if;

  _<x> := PolynomialRing(Parent(zeta));
  F_file := CURR_DIR cat "f_abc/" cat Sprint(D) cat ".txt";
  F := eval Read(F_file);
  return F;
end intrinsic;
