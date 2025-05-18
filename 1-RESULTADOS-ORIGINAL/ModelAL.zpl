set F := {1,2,3,4,5}; # set of factory indices, where the last one corresponds to the distribution center
set P := {1,2,3,4,5,6};  # set of product indices
set D := {0 .. 30};  # set of day indices
set T := {1 ..4};  # set of vehicle type indices
set K := {1,2,3,4,5};  # maximum number of vehicles (of any type)  

set Pi := {1,3,5,6};  # primary products
set Pd := {2,4};  # derived products

set TP := T*P;

set FT := F*T;

param FF[F*F] := <1,3> 1, <1,4> 1, <1,5> 1, <2,5> 1, <3,1> 1, <3,5> 1, <4,5> 1 default 0;
param TT[F*F] := <1,3> 1, <1,4> 2, <1,5> 2, <2,5> 2, <3,1> 1, <3,5> 2, <4,5> 1 default 0;
param CTP[TP] := <1,1> 21.168, <1,2> 22.680, <1,5> 17.2032, 
                 <2,1> 12.096, <2,2> 12.960, <2,5> 9.8304,
                 <3,3> 25,
                 <4,3> 50, <4,4> 50, <4,6> 50 default 0;
param VFT[FT] := <1,1> 3, <1,2> 2, <1,3> 5, 
                 <2,1> 3, <2,2> 2,
                 <3,1> 3, <3,2> 2,
                 <4,4> 4 default 0;  
param FP[F*P] := <1,1> 1, <1,2> 1, <1,3> 1, <2,5> 1, <3,1> 1, <3,2> 1, <4,3> 1, <4,4> 1, <4,6> 1 default 0;

set FPD := { <f,p,d> in F*P*D with FP[f,p] == 1 or f == 5};
set FPiD := { <f,p,d> in F*Pi*D with FP[f,p] == 1 };
set FPDFTK := { <f,p,d,fl,t,k> in F*P*D*F*T*K with f != fl and FF[f,fl] == 1 and VFT[f,t] > 0 and k <= VFT[f,t] and (FP[f,p] == 1 or f==5)};
set PP := { <p,pl> in P*P with p != pl};  
set PD := P*D;

set FTK := { <f,t,k> in F*T*K with   VFT[f,t] > 0 and k <= VFT[f,t] };

param a[PP] := <1,2> 1, <3,4> 1 default 0;     # determines whether product pl uses product p as raw material
set FPiPdD := { <f,pi,pd,d> in F*Pi*Pd*D with  FP[f,pd] == 1  and a[pi,pd]==1 };
param TQ[P] := <1> 20, <3> 3, <5> 5, <6> 2 default 0; # product quarantine time
param Dem[P] := <1> 420, <2> 200, <3> 300, <4> 200, <5> 130, <6> 380;
param CF[F*P] := <1,1> 80, <1,2> 21.420, <1,3> 50, <2,5> 16, <3,1> 80, <3,2> 21.420, 
                 <4,3> 50, <4,4> 40, <4,6> 20 default 0; 
param I0[F*P] := <5,1> 80, <1,1> 80, <3,1> 80,
                 <5,2> 21.420, <1,2> 21.420, <3,2> 21.420,
                 <5,3> 50, <1,3> 50, <4,3> 50, 
				 <5,4> 40, <4,4> 40,
				 <5,5> 16, <2,5> 16,
				 <5,6> 20, <4,6> 20 default 0;
var I[FPD] >=0;  # variable for the inventory of product p at factory f on day d
var Q[<f,p,d> in FPD] >=0 <= if d <= TQ[p]+1 then 0 else Dem[p] end;  # variable that determines the quantity of product p released from quarantine on day d at factory f
var yd[<f,pi,pd,d> in FPiPdD] >=0 <= CF[f,pd]; # variable for the quantity of product pd produced from pi at factory f on day d
var yi[<f,p,d> in FPiD] >=0 <= CF[f,p]; # variable that determines the quantity of product p produced at factory f on day d
var x[FPDFTK] >=0; # variable that determines the quantity of product p leaving factory f and going to factory fl on day d 
var x2[<f,p,d,fl,t,k> in FPDFTK] >=0 <= if d <= TT[f,fl] then 0 else Dem[p] end; # variable that determines the quantity of product p arriving at factory fl from factory f on day d 
var Tmax >=0;
var w[PD] binary;
var z[FPDFTK] binary;

minimize fo : Tmax + 0.0001 * sum <f,p,d> in FPiD : yi[f,p,d];


subto c1a: forall <f,p,d> in FPD with d > 0 and f < 5 do
             I[f,p,d] == I[f,p,d-1] + Q[f,p,d] + sum<fl,p,d,f,t,k> in FPDFTK : x2[fl,p,d,f,t,k] 
                        - sum <f,p,d,fl,t,k> in FPDFTK : x[f,p,d,fl,t,k] 
                        - sum <f,p,pd,d> in FPiPdD :  yd[f,p,pd,d]; 

subto c2a: forall <f,pi,pd,d> in FPiPdD with d + TQ[pd]+1 <= card(D)-1 do
             yd[f,pi,pd,d] == Q[f,pd,d+TQ[pd]+1];

subto c2b: forall <f,p,d> in FPiD with d + TQ[p]+1   <= card(D)-1 do
             yi[f,p,d] == Q[f,p,d+TQ[p]+1];

subto c2c: forall <f,p,d,fl,t,k> in FPDFTK with d + TT[f,fl]  <= card(D)-1 do
              x[f,p,d,fl,t,k] == x2[f,p,d+TT[f,fl],fl,t,k];

subto c3: forall <f,p,d,fl,t,k> in FPDFTK do
             x[f,p,d,fl,t,k] <= CTP[t,p];  # it is necessary to consider transportation time

subto c4: forall <5,p,d> in FPD with d > 0 do  # constraint regarding inventory at the distribution center (DC)
             I[5,p,d] == I[5,p,d-1] +  sum <f,p,d,5,t,k> in FPDFTK : x2[f,p,d,5,t,k]; 
                        
subto c5: forall <p> in P do 
           sum <p,d> in PD : w[p,d] == 1; 

subto c6: forall <5,p,d> in FPD do 
             I[5,p,d] >=  Dem[p] * w[p,d]; 

subto c7: forall <p,d> in PD do
             d*w[p,d] <= Tmax;

subto c8: forall <f> in F with f < 5 do  # initial inventory
             forall <p> in P with FP[f,p] == 1 do
                I[f,p,0] == I0[f,p];

subto c9: forall <p> in P do  # initial inventory at the DC
                I[5,p,0] == I0[5,p];

subto c10: forall <f,p,d,fl,t,k> in FPDFTK do 
              x[f,p,d,fl,t,k] <= CTP[t,p] * z[f,p,d,fl,t,k];
			  
subto c11: forall <f,p,d,fl,t,k> in  FPDFTK  do
              z[f,p,d,fl,t,k] + 
              sum <f,pp,dd,ffll,t,k> in FPDFTK with dd>d and dd <=d+TT[f,fl]-1 : z[f,pp,dd,ffll,t,k] <=1;
