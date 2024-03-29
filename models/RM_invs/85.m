A1 := (g-1)^2*(g+1)^2*(h-1)*(h+1)*(g*h-g+2)^2*(g^2*h+h-g^2+2*g+1)^2
    *(g^2*h+g*h+h-g^2+g+1)^2;
A :=  -(g-1)^2*(g+1)^2
    *(25*g^4*h^4-30*g^3*h^4-5*g^2*h^4-30*g*h^4+25*h^4-20*g^4*h^3
    -60*g^3*h^3-120*g^2*h^3+60*g*h^3+20*h^3-84*g^4*h^2
    -58*g^3*h^2+34*g^2*h^2+58*g*h^2-24*h^2+16*g^4*h+76*g^3*h
    +120*g^2*h-44*g*h-16*h+64*g^4+80*g^3-7*g^2-20*g+4)/3;
B1 := -(g-1)^2*(g+1)^2*(h-1)*(h+1)
    *(3*g^16*h^8+6*g^15*h^8+13*g^14*h^8+14*g^13*h^8+18*g^12*h^8+8*g^11*h^8
    +2*g^10*h^8-28*g^9*h^8-24*g^8*h^8-28*g^7*h^8+2*g^6*h^8
    +8*g^5*h^8+18*g^4*h^8+14*g^3*h^8+13*g^2*h^8+6*g*h^8+3*h^8
    -24*g^16*h^7-6*g^15*h^7-4*g^14*h^7+76*g^13*h^7+86*g^12*h^7
    +138*g^11*h^7+40*g^10*h^7+20*g^9*h^7-204*g^8*h^7
    -184*g^7*h^7-140*g^6*h^7+2*g^5*h^7+118*g^4*h^7+100*g^3*h^7
    +104*g^2*h^7+46*g*h^7+24*h^7+84*g^16*h^6-126*g^15*h^6
    -83*g^14*h^6-222*g^13*h^6+101*g^12*h^6+244*g^11*h^6
    +491*g^10*h^6+156*g^9*h^6-58*g^8*h^6-572*g^7*h^6
    -737*g^6*h^6-140*g^5*h^6+49*g^4*h^6+462*g^3*h^6
    +281*g^2*h^6+198*g*h^6+64*h^6-168*g^16*h^5+546*g^15*h^5
    -146*g^14*h^5-196*g^13*h^5-728*g^12*h^5-454*g^11*h^5
    +450*g^10*h^5+900*g^9*h^5+644*g^8*h^5-636*g^7*h^5
    -898*g^6*h^5-1378*g^5*h^5+108*g^4*h^5+592*g^3*h^5
    +658*g^2*h^5+434*g*h^5+80*h^5+210*g^16*h^4-1050*g^15*h^4
    +1205*g^14*h^4+670*g^13*h^4-405*g^12*h^4-700*g^11*h^4
    -1931*g^10*h^4+500*g^9*h^4+990*g^8*h^4+1120*g^7*h^4
    -1179*g^6*h^4-1520*g^5*h^4-609*g^4*h^4+430*g^3*h^4
    +1165*g^2*h^4+550*g*h^4+74*h^4-168*g^16*h^3+1134*g^15*h^3
    -2288*g^14*h^3+276*g^13*h^3+2862*g^12*h^3-642*g^11*h^3
    -76*g^10*h^3-2564*g^9*h^3-308*g^8*h^3+1312*g^7*h^3
    +136*g^6*h^3-786*g^5*h^3-1466*g^4*h^3+516*g^3*h^3
    +1204*g^2*h^3+562*g*h^3+104*h^3+84*g^16*h^2-714*g^15*h^2
    +2059*g^14*h^2-1546*g^13*h^2-2701*g^12*h^2+3884*g^11*h^2
    +637*g^10*h^2-684*g^9*h^2-1038*g^8*h^2-1148*g^7*h^2
    +1057*g^6*h^2-620*g^5*h^2-857*g^4*h^2+274*g^3*h^2
    +823*g^2*h^2+554*g*h^2+128*h^2-24*g^16*h+246*g^15*h
    -922*g^14*h+1252*g^13*h+724*g^12*h-3266*g^11*h+1186*g^10*h
    +2284*g^9*h-868*g^8*h-364*g^7*h-282*g^6*h-270*g^5*h
    -360*g^4*h-56*g^3*h+466*g^2*h+366*g*h+80*h+3*g^16-36*g^15
    +166*g^14-324*g^13+43*g^12+788*g^11-799*g^10-584*g^9
    +930*g^8+244*g^7-263*g^6-160*g^5-201*g^4-28*g^3+150*g^2
    +100*g+19)/3;
B :=  -2*(g-1)^2*(g+1)^2
    *(98*g^8*h^6-252*g^7*h^6+445*g^6*h^6+252*g^5*h^6-978*g^4*h^6+252*g^3*h^6
    +445*g^2*h^6-252*g*h^6+98*h^6-42*g^8*h^5+1179*g^7*h^5
    +345*g^6*h^5-2583*g^5*h^5-252*g^4*h^5+1449*g^3*h^5-93*g^2*h^5
    +171*g*h^5+42*h^5+345*g^8*h^4+897*g^7*h^4-2643*g^6*h^4
    -1377*g^5*h^4+2346*g^4*h^4+117*g^3*h^4+129*g^2*h^4+363*g*h^4
    -285*h^4-56*g^8*h^3-2838*g^7*h^3-1162*g^6*h^3+3882*g^5*h^3
    +1260*g^4*h^3-906*g^3*h^3+154*g^2*h^3-570*g*h^3-196*h^3
    -969*g^8*h^2-1503*g^7*h^2+2349*g^6*h^2+2013*g^5*h^2-726*g^4*h^2
    -249*g^3*h^2-927*g^2*h^2-261*g*h^2+165*h^2+84*g^8*h+1707*g^7*h
    +717*g^6*h-1347*g^5*h-1008*g^4*h-591*g^3*h+39*g^2*h+447*g*h
    +168*h+539*g^8+798*g^7-107*g^6-964*g^5-756*g^4-44*g^3+397*g^2
    +210*g+35)/27;
B2 := -(g-1)^2*(g+1)^2*(h-1)*(h+1);

return [A, A1, B, B1, B2];
