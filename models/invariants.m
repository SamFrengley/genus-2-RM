CURR_DIR := "THIS/NEEDS/TO/CONTAIN/THE/PATH/ENDING/AT/models";

function IsFundDiscriminant(D)
  if not (D mod 4) in [0,1] then
    return false;
  end if;

  if D mod 4 eq 1 then
    if IsSquarefree(D) then
      return true;
    else
      return false;
    end if;
  elif D mod 4 eq 0 then
    if IsSquarefree(D div 4) then
      return true;
    else
      return false;
    end if;
  end if;
end function;


function WasComputedByEK(D)
  //Returns true if Y_(D) was computed by Elkies--Kumar
  if D ge 100 then
    return false;
  end if;

  return IsFundDiscriminant(D);
end function;


intrinsic GetRMInvariants(D::RngIntElt : coords:=[]) -> SeqEnum
{
  Returns the invariants A, A1, B, B1, B2 of Elkies--Kumar.
}
  require IsFundDiscriminant(D): "That's not a fund. discriminant";
  require WasComputedByEK(D): "That's > 100";
  require D ne 33: "The RM invariants weren't given for D=33 by Elkies--Kumar";
  require #coords in [0,2]: "You need to give two variables (g,h)";
  
  if #coords eq 0 then
    KK<g,h> := FunctionField(Rationals(), 2);
  else
    g,h := Explode(coords);
  end if;
  
  return eval Read(CURR_DIR cat "RM_invs/" cat Sprint(D) cat ".m");
end intrinsic;


intrinsic GetIgusaClebschInvariants(D::RngIntElt : coords:=[]) -> SeqEnum
{
  Returns the Igusa--Clebsch invariants associated to RM D.
}
  require IsFundDiscriminant(D): "That's not a fund. discriminant";
  require WasComputedByEK(D): "That's > 100";
  require #coords in [0,2]: "You need to give two variables (g,h)";
  
  if #coords eq 0 then
    KK<g,h> := FunctionField(Rationals(), 2);
  else
    g,h := Explode(coords);
  end if;
  
  if D eq 33 then
  ICs := eval Read(CURR_DIR cat "IC_invs/33.txt");
  else
    A, A1, B, B1, B2 := Explode(GetRMInvariants(D : coords:=[g,h]));
    ICs := [-24*B1/A1, -12*A, 96*(A/A1)*B1-36*B, -4*A1*B2];
  end if;

  return ICs;
end intrinsic;
