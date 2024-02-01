CURR_DIR := "THIS/NEEDS/TO/CONTAIN/THE/PATH/ENDING/AT/models";

intrinsic Getq_D(D::RngIntElt : coords:=[]) -> RngMPolElt
{
  Return the polynomial q_D ∈ ℚ[g,h].
}
  require D in [5,8,12,13,17,21,24,28,29,33,37,44,53,61]: "D is not in our little database";
  if #coords eq 0 then
    _<g,h> := PolynomialRing(Rationals(), 2);
  else
    require #coords eq 2: "Coords should have two elements, g and h";
    g,h := Explode(coords);
  end if;
  
  q_file := CURR_DIR cat "q/" cat Sprint(D) cat ".txt";
  q := eval Read(q_file);

  return q;
end intrinsic;


intrinsic Getp_D(D::RngIntElt : coords:=[]) -> RngMPolElt
{
  Return the polynomial p_D ∈ ℚ[m,n].
}
  require D in [5,8,12,13,17,21,24,28,29,33,37,44,53,61]: "D is not in our little database";
  if #coords eq 0 then
    _<m,n> := PolynomialRing(Rationals(), 2);
  else
    require #coords eq 2: "Coords should have two elements, g and h";
    m,n := Explode(coords);
  end if;
  
  p_file := CURR_DIR cat "p/" cat Sprint(D) cat ".txt";
  p := eval Read(p_file);

  return p;
end intrinsic;


intrinsic Getlambda_D(D::RngIntElt : coords:=[]) -> RngMPolElt
{
  Get the polynomial λ ∈ ℚ[g,h].
}
  require D in [5,8,12,13,17,21,24,28,29,33,37,44,53,61]: "D is not in our little database";
  if #coords eq 0 then
    _<g,h> := PolynomialRing(Rationals(), 2);
  else
    require #coords eq 2: "Coords should have two elements, g and h";
    g,h := Explode(coords);
  end if;
  
  l_file := CURR_DIR cat "lambda/" cat Sprint(D) cat ".txt";
  l := eval Read(l_file);

  return l;
end intrinsic;


intrinsic Get_xi_phi(D::RngIntElt : coords:=[]) -> RngMPolElt
{
  Get the polynomials ξ∈ ℚ[g,h] and φ ∈ L[x] where L = ℚ[g,h][r]/ξ(r), 
  so that f_D = Nm_(L/K) φ.
}
  require D in [8,12]: "This representation is only known when D=8,12";
  if #coords eq 0 then
    _<a,b,c> := PolynomialRing(Rationals(), 3);
  else
    require #coords eq 3: "Coords should have three elements, a,b,c";
    a,b,c := Explode(coords);
  end if;

  k := FieldOfFractions(Parent(a));
  P<r> := PolynomialRing(k);

  xi_file := CURR_DIR cat "xi_and_phi/" cat Sprint(D) cat "/xi.txt";
  xi := eval Read(xi_file);

  L<r> := quo<P | xi>;
  PP<x> := PolynomialRing(L);

  phi_file := CURR_DIR cat "xi_and_phi/" cat Sprint(D) cat "/phi.txt";
  phi := eval Read(phi_file);

  return phi, xi;
end intrinsic;


intrinsic GetTransformedMestreConic(D::RngIntElt: coords:=[], rat:=false) -> RngMPolElt
{
  Gets the transformed Mestre conic, transformed using our found transforms.
}
  if not rat then
    require D in [5,8,12,13,17,21,24,28,29,33,37,44,53,61]: "D is not in our little database";
    if #coords eq 0 then
      _<g,h,z> := PolynomialRing(Rationals(), 3);
    elif #coords eq 2 then
      g,h := Explode(coords);
    else
      require #coords eq 3: "Coords should have two elements, g and h";
      g,h,z := Explode(coords);
    end if;

    P2<X,Y,Z> := PolynomialRing(Parent(g), 3);
    q := Getq_D(D : coords:=[g,h]);
    return X^2 - D*Y^2 - q*Z^2;

  else
    require D in [5,8,12,13,17]: "D is not in our little database";
    if #coords eq 0 then
      _<m,n> := PolynomialRing(Rationals(), 2);
    else
      require #coords eq 2: "Coords should have two elements, m and n";
      m,n := Explode(coords);
    end if;

    P2<X,Y,Z> := PolynomialRing(Parent(m), 3);
    p := Getp_D(D : coords:=[m,n]);
    return X^2 - D*Y^2 - p*Z^2;
    
  end if;
end intrinsic;


intrinsic GetTransformedMestreCubic(D::RngIntElt: coords:=[], rat:=false) -> RngMPolElt
{
  Gets the transformed Mestre cubic, transformed using our found transforms.
}
  if not rat then
    require D in [5,8,12,13,17,21,24,28,29,33,37,44,53,61]: "D is not in our little database";
    if #coords eq 0 then
      _<g,h,z> := PolynomialRing(Rationals(), 3);
    else
      require #coords eq 3: "Coords should have three elements, g and h, z";
      g,h,z := Explode(coords);
    end if;

    P2<X,Y,Z> := PolynomialRing(Parent(g), 3);
    cubic_file := CURR_DIR cat "transformed-cubic/" cat Sprint(D) cat ".txt";
    return eval Read(cubic_file);

  else
    require D in [5,8,12,13,17]: "D is not in our little database";
    if #coords eq 0 then
      _<m,n> := PolynomialRing(Rationals(), 2);
    else
      require #coords eq 2: "Coords should have two elements, m and n";
      m,n := Explode(coords);
    end if;

    P2<X,Y,Z> := PolynomialRing(Parent(m), 3);
    cubic_file := CURR_DIR cat "transformed-cubic_rat/" cat Sprint(D) cat ".txt";
    return eval Read(cubic_file);
  end if;
end intrinsic;


intrinsic GetHMSParam(D::RngIntElt : coords:=[]) -> SeqEnum
{
  Get the Elkies--Kumar parametrisation (m,n) -> (g,h) for Y_(D)
}
  require D in [5,8,12,13,17]: "Y_(D) is not rational";
  if #coords eq 0 then
    _<m,n> := FunctionField(Rationals(), 2);
  else
    require #coords eq 2: "Coords should have two elements, g and h";
    m,n := Explode(coords);
  end if;
  
  file := CURR_DIR cat "HMS_param/" cat Sprint(D) cat ".m";
  ret := eval Read(file);

  return ret;
end intrinsic;
