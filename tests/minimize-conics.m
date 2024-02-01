/**************************************************
This is a sample usage of the MinimizationSearch 
algorithm.
**************************************************/
AttachSpec("../minimize/spec");
AttachSpec("../models/spec");

QQ := Rationals();
K<g,h> := FunctionField(Rationals(), 2);

print "Using verbose printing so we can see what's happening";
SetVerbose("ConicMinimize", 2);

DISCRIMINANTS := [5, 13, 28];

for D in DISCRIMINANTS do
  print "\n\n============================";
  printf "Testing the case when D=%o\n", D;
  print "============================";
  
  ICs := GetIgusaClebschInvariants(D : coords:=[g,h]);
  L := ICConic(ICs);
  _ := MinimizationSearch(L : maxsteps := 100);

  print "\n\nWait a few seconds so you can view above.\n";
  Pipe("sleep 10", "");
end for;
