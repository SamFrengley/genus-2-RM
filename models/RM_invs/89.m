A1 := 2*(h-1)^2*(h-g-2)^2*(g*h+1)^2*(g*h^2+h^2-g^2*h-2*g*h-2*h+1)^2;
A := -(g^4*h^8+4*g^3*h^8+6*g^2*h^8+4*g*h^8+h^8-4*g^5*h^7-12*g^4*h^7-24*g^3*h^7
    -40*g^2*h^7-36*g*h^7-12*h^7+6*g^6*h^6+12*g^5*h^6-2*g^4*h^6+36*g^3*h^6
    +150*g^2*h^6+160*g*h^6+54*h^6-4*g^7*h^5-4*g^6*h^5+48*g^5*h^5
    +156*g^4*h^5+52*g^3*h^5-516*g^2*h^5-576*g*h^5-116*h^5+g^8*h^4
    -24*g^6*h^4-372*g^5*h^4-716*g^4*h^4+500*g^3*h^4+1894*g^2*h^4
    +1140*g*h^4+129*h^4-4*g^7*h^3+216*g^6*h^3+1072*g^5*h^3+1612*g^4*h^3
    -40*g^3*h^3-1796*g^2*h^3-1036*g*h^3-72*h^3+6*g^6*h^2-432*g^5*h^2
    -1336*g^4*h^2-1012*g^3*h^2+238*g^2*h^2+344*g*h^2+16*h^2-4*g^5*h
    +216*g^4*h+436*g^3*h+208*g^2*h+g^4)/3;
B1 := -2*(g^6*h^14+4*g^5*h^14+6*g^4*h^14+4*g^3*h^14+g^2*h^14-6*g^7*h^13-30*g^6*h^13
    -68*g^5*h^13-94*g^4*h^13-84*g^3*h^13-44*g^2*h^13-10*g*h^13
    +15*g^8*h^12+80*g^7*h^12+233*g^6*h^12+484*g^5*h^12+787*g^4*h^12
    +894*g^3*h^12+574*g^2*h^12+152*g*h^12+h^12-20*g^9*h^11-90*g^8*h^11
    -258*g^7*h^11-870*g^6*h^11-2416*g^5*h^11-4738*g^4*h^11
    -5838*g^3*h^11-3878*g^2*h^11-1060*g*h^11-16*h^11+15*g^10*h^10
    +20*g^9*h^10-147*g^8*h^10+108*g^7*h^10+3082*g^6*h^10
    +10636*g^5*h^10+20934*g^4*h^10+25018*g^3*h^10+16244*g^2*h^10
    +4466*g*h^10+112*h^10-6*g^11*h^9+46*g^10*h^9+552*g^9*h^9
    +1350*g^8*h^9-1194*g^7*h^9-13120*g^6*h^9-36740*g^5*h^9
    -64866*g^4*h^9-72730*g^3*h^9-45564*g^2*h^9-12564*g*h^9-456*h^9
    +g^12*h^8-40*g^11*h^8-429*g^10*h^8-1396*g^9*h^8-274*g^8*h^8
    +10622*g^7*h^8+38575*g^6*h^8+85422*g^5*h^8+137205*g^4*h^8
    +145922*g^3*h^8+88649*g^2*h^8+24702*g*h^8+1218*h^8+10*g^12*h^7
    +110*g^11*h^7+382*g^10*h^7-260*g^9*h^7-6384*g^8*h^7-25242*g^7*h^7
    -63332*g^6*h^7-126760*g^5*h^7-196786*g^4*h^7-203462*g^3*h^7
    -121252*g^2*h^7-34692*g*h^7-2280*h^7+g^12*h^6+32*g^11*h^6
    +358*g^10*h^6+2180*g^9*h^6+8453*g^8*h^6+23804*g^7*h^6
    +56952*g^6*h^6+120070*g^5*h^6+191421*g^4*h^6+196392*g^3*h^6
    +116323*g^2*h^6+35118*g*h^6+3108*h^6-46*g^10*h^5-484*g^9*h^5
    -2480*g^8*h^5-9198*g^7*h^5-29632*g^6*h^5-74772*g^5*h^5
    -125524*g^4*h^5-128434*g^3*h^5-76760*g^2*h^5-25650*g*h^5-3144*h^5
    +10*g^10*h^4+80*g^9*h^4+442*g^8*h^4+2434*g^7*h^4+10993*g^6*h^4
    +31402*g^5*h^4+53287*g^4*h^4+53588*g^3*h^4+33283*g^2*h^4
    +13474*g*h^4+2361*h^4-46*g^8*h^3-510*g^7*h^3-2760*g^6*h^3
    -7828*g^5*h^3-12462*g^4*h^3-11988*g^3*h^3-8610*g^2*h^3-5072*g*h^3
    -1288*h^3+g^8*h^2+32*g^7*h^2+234*g^6*h^2+578*g^5*h^2+619*g^4*h^2
    +490*g^3*h^2+1078*g^2*h^2+1360*g*h^2+484*h^2+10*g^6*h+84*g^5*h
    +222*g^4*h+224*g^3*h-60*g^2*h-248*g*h-112*h+g^4+4*g^3+16*g^2+24*g
    +12)/3;
B := 2*(g^6*h^12+6*g^5*h^12+15*g^4*h^12+20*g^3*h^12+15*g^2*h^12+6*g*h^12+h^12
    -6*g^7*h^11-30*g^6*h^11-78*g^5*h^11-150*g^4*h^11-210*g^3*h^11
    -186*g^2*h^11-90*g*h^11-18*h^11+15*g^8*h^10+60*g^7*h^10
    +114*g^6*h^10+234*g^5*h^10+606*g^4*h^10+1104*g^3*h^10+1146*g^2*h^10
    +618*g*h^10+135*h^10-20*g^9*h^9-60*g^8*h^9+18*g^7*h^9+220*g^6*h^9
    -678*g^5*h^9-2988*g^4*h^9-4218*g^3*h^9-3468*g^2*h^9-1950*g*h^9
    -552*h^9+15*g^10*h^8+30*g^9*h^8-177*g^8*h^8-324*g^7*h^8+729*g^6*h^8
    +7620*g^5*h^8+13536*g^4*h^8+6372*g^3*h^8-270*g^2*h^8+1494*g*h^8
    +1359*h^8-6*g^11*h^7-6*g^10*h^7+138*g^9*h^7-858*g^8*h^7
    -3504*g^7*h^7-2664*g^6*h^7+5712*g^5*h^7+22752*g^4*h^7+37458*g^3*h^7
    +28914*g^2*h^7+6234*g*h^7-2106*h^7+g^12*h^6-24*g^10*h^6
    +1398*g^9*h^6+5673*g^8*h^6-3828*g^7*h^6-73210*g^6*h^6
    -188904*g^5*h^6-241083*g^4*h^6-185008*g^3*h^6-87678*g^2*h^6
    -17970*g*h^6+2073*h^6-6*g^11*h^5-540*g^10*h^5-2646*g^9*h^5
    -1224*g^8*h^5+45696*g^7*h^5+212208*g^6*h^5+445992*g^5*h^5
    +512712*g^4*h^5+336654*g^3*h^5+123744*g^2*h^5+20142*g*h^5-1260*h^5
    +15*g^10*h^4+2160*g^9*h^4+2736*g^8*h^4-47520*g^7*h^4-231363*g^6*h^4
    -476334*g^5*h^4-516261*g^4*h^4-301356*g^3*h^4-89109*g^2*h^4
    -10740*g*h^4+432*h^4-20*g^9*h^3-3240*g^8*h^3+1518*g^7*h^3
    +69270*g^6*h^3+197190*g^5*h^3+235674*g^4*h^3+132236*g^3*h^3
    +31380*g^2*h^3+2256*g*h^3-64*h^3+15*g^8*h^2+2160*g^7*h^2
    -504*g^6*h^2-21366*g^5*h^2-37221*g^4*h^2-23052*g^3*h^2-4488*g^2*h^2
    -6*g^7*h-540*g^6*h-1074*g^5*h-552*g^4*h+g^6)/27;
B2 := -512*g^2*(g+1)^3*h^5;

return [A, A1, B, B1, B2];
