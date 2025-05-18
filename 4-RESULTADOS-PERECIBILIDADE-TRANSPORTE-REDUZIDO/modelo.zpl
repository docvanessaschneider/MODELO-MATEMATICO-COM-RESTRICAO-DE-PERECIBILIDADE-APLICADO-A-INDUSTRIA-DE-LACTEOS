set F := {1,2,3,4,5}; # conjunto de indices das fabricas, em que a ultima corresponde ao centro de distribuicao
set P := {1,2,3,4,5,6}; # conjunto de indices dos produtos
set D := {0 .. 30}; # conjunto de indices dos dias
set T := {1 ..4}; # conjunto de indices dos tipo de veiculos
set K := {1,2,3,4,5}; # qdte maxima de veiculos (de qq tipo)

set Pi := {1,3,5,6}; # produtos primarios
set Pd := {2,4}; # produtos derivados

set TP := T*P;

set FT := F*T;

param FF[F*F] := <1,3> 1, <1,4> 1, <1,5> 1, <2,5> 1, <3,1> 1, <3,5> 1, <4,5> 1 default 0; #rotas possíveis saindo da fábrica de origem f para fábrica destino f'
param TT[F*F] := <1,3> 1, <1,4> 2, <1,5> 2, <2,5> 2, <3,1> 1, <3,5> 2, <4,5> 1 default 0; #tempo de transporte entre fábrica origem e fábrica destino
param CTP[TP] := <1,1> 21.168, <1,2> 22.68, <1,5> 17.2032, <2,1> 12.096, <2,2> 12.96, <2,5> 9.8304, <3,3> 25, <4,3> 50, <4,4> 50, <4,6> 50 default 0; #capacidade do tipo do veículo t para transporte do produto p
param VFT[FT] := <1,1> 2, <1,2> 1, <1,3> 1, <2,1> 1, <2,2> 1, <3,1> 2, <3,2> 1, <4,4> 1 default 0;  #para cada fábrica de origem cada tipo de veículo a quantidade disponível
param FP[F*P] := <1,1> 1, <1,2> 1, <1,3> 1, <2,5> 1, <3,1> 1, <3,2> 1, <4,3> 1, <4,4> 1, <4,6> 1 default 0; #fábrica que produz determinado produto

set FPD := { <f,p,d> in F*P*D with FP[f,p] == 1 or f == 5};
set FPiD := { <f,p,d> in F*Pi*D with FP[f,p] == 1 };
set FPDFTK := { <f,p,d,fl,t,k> in F*P*D*F*T*K with f != fl and FF[f,fl] == 1 and VFT[f,t] > 0 and k <= VFT[f,t] and (FP[f,p] == 1 or f==5)};
set FDFT := { <f,d,fl,t> in F*D*F*T with f != fl and FF[f,fl] == 1 and VFT[f,t] > 0 };
set PP := { <p,pl> in P*P with p != pl};  
set PD := P*D;

set FTK := { <f,t,k> in F*T*K with VFT[f,t] > 0 and k <= VFT[f,t] };

param aa[P*F] := <1,1> 1, <1,3> 1, <3,4> 1 default 0;  # determina se o produto p é utilizado comno materia prima na fabrica f 

param a[PP] := <1,2> 1, <3,4> 1 default 0;     # determina se o produto pl utiliza o produto p com materia prima
set FPiPdD := { <f,pi,pd,d> in F*Pi*Pd*D with FP[f,pd] == 1 and a[pi,pd]==1 };
param TQ[P] := <1> 20, <3> 3, <5> 5, <6> 2 default 0; # tempo de quarentena do produto
param Dem[P] := <1> 420, <2> 200, <3> 300, <4> 200, <5> 130, <6> 380; #demanda do centro de distribuição do produto p
param CF[F*P] := <1,1> 80, <1,2> 21.42, <1,3> 50, <2,5> 16, <3,1> 80, <3,2> 21.42, <4,3> 50, <4,4> 40, <4,6> 20 default 0; #capacidade das fábricas f para produzir o produto p
param I0[F*P] := <5,1> 80, <1,1> 80, <3,1> 80, <5,2> 21.42, <1,2> 21.42, <3,2> 21.42, <5,3> 50, <1,3> 50, <4,3> 50, <5,4> 40, <4,4> 40, <5,5> 16, <2,5> 16, <5,6> 20, <4,6> 20 default 0; #estoque inicial em cada fábrica f de cada produto p
var I[FPD] >=0;  # variavel do estoque do produto p na fabrica f no dia d
var Q[<f,p,d> in FPD] >=0 <= if d <= TQ[p]+1 then 0 else Dem[p] end;  # variavel que determina a quantidade do produto p que eh liberada da quarentena no dia d na frab f
var yd[<f,pi,pd,d> in FPiPdD] >=0 <= CF[f,pd]; # var qtde produzida do produto p no dia d na frab f
var yi[<f,p,d> in FPiD] >=0 <= CF[f,p]; # var que determina a qtde produzida do produto p no dia d na frab f
var x[<f,p,d,fl,t,k> in FPDFTK] >=0 <= if (aa[p,fl] == 1 or fl == 5) then infinity else 0 end; # variavel que determina a quantidade do produto p que sai da fab f e vai para a fab fl no no dia d 
var x2[<f,p,d,fl,t,k> in FPDFTK] >=0 <= if d <= TT[f,fl] then 0 else Dem[p] end; # var que determina a qtde do produto p que chega na fab fl vindo da fab f no no dia d 
var Tmax >=0;
var w[PD] binary;
var z[FPDFTK] binary;

minimize fo : Tmax + 0.000001 * sum<f,p,d,fl,t,k> in FPDFTK with fl < 5 : x[f,p,d,fl,t,k] + 0.0001 * sum <f,p,d> in FPiD : yi[f,p,d];

subto c1a: forall <f,p,d> in FPD with d > 0 and f < 5 do
             I[f,p,d] == I[f,p,d-1] + Q[f,p,d] + sum<fl,p,d,f,t,k> in FPDFTK : x2[fl,p,d,f,t,k] 
                        - sum <f,p,d,fl,t,k> in FPDFTK : x[f,p,d,fl,t,k] 
                        - sum <f,p,pd,d> in FPiPdD :  yd[f,p,pd,d]; 

subto c1b0: forall <f,p,d> in FPD with d == 0 and f < 5 do # tem q enviar em ate 7 dias devido a ser perecivel 
              I[f,p,0] <= sum <f,p,dl,fl,t,k> in FPDFTK with dl >= 1 and dl <= 6: x[f,p,dl,fl,t,k] 
                        + sum <f,p,pd,dl> in FPiPdD with dl >= 1 and dl <= 6:  yd[f,p,pd,dl]; 

subto c1b: forall <f,p,d> in FPD with f < 5 and d > 0 and d < 24 do # tem q enviar em ate 7 dias devido a ser perecivel 
              I[f,p,d+6] <=  sum <fl,p,dl,f,t,k> in FPDFTK with dl >= d+1 and dl <= d+6: x2[fl,p,dl,f,t,k] 
                           + sum <f,p,pd,dl> in FPiPdD with dl >= d+1 and dl <= d+6:  yd[f,p,pd,dl]; 

subto c2a0: forall <f,pi,pd,d> in FPiPdD with d + TQ[pd]+1 <= card(D)-1 do
             sum<fl,pi,d,f,t,k> in FPDFTK with a[pi,pd]==1: x2[fl,pi,d,f,t,k] <= yd[f,pi,pd,d];

subto c2a: forall <f,pi,pd,d> in FPiPdD with d + TQ[pd]+1 <= card(D)-1 do
             yd[f,pi,pd,d] == Q[f,pd,d+TQ[pd]+1];

subto c2b: forall <f,p,d> in FPiD with d + TQ[p]+1 <= card(D)-1 do
             yi[f,p,d] == Q[f,p,d+TQ[p]+1];

subto c2c: forall <f,p,d,fl,t,k> in FPDFTK with d + TT[f,fl] <= card(D)-1 do
              x[f,p,d,fl,t,k] == x2[f,p,d+TT[f,fl],fl,t,k];

subto c3: forall <f,p,d,fl,t,k> in FPDFTK do
             x[f,p,d,fl,t,k] <= CTP[t,p];  # necessario considerar o tempo de transporte 

subto c4: forall <5,p,d> in FPD with d > 0 do  # restricao referente ao estoque no CD
             I[5,p,d] == I[5,p,d-1] + sum <f,p,d,5,t,k> in FPDFTK : x2[f,p,d,5,t,k]; 

subto c5: forall <p> in P do 
           sum <p,d> in PD : w[p,d] == 1; 

subto c6: forall <5,p,d> in FPD do 
             I[5,p,d] >= Dem[p] * w[p,d]; 

subto c7: forall <p,d> in PD do
             d*w[p,d] <= Tmax;

subto c8: forall <f> in F with f < 5 do  # estoque inicial
             forall <p> in P with FP[f,p] == 1 do
                I[f,p,0] == I0[f,p];

subto c9: forall <p> in P do  # estoque inicial no CD
                I[5,p,0] == I0[5,p];

subto c10: forall <f,p,d,fl,t,k> in FPDFTK do 
              x[f,p,d,fl,t,k] <= CTP[t,p] * z[f,p,d,fl,t,k];

subto c11: forall <f,d,fl,t> in FDFT do
              sum <f,p,d,fl,t,k> in FPDFTK : z[f,p,d,fl,t,k] <= VFT[f,t];

subto c12: forall <f,p,d,fl,t,k> in FPDFTK do
              z[f,p,d,fl,t,k] + 
              sum <f,pp,dd,ffll,t,k> in FPDFTK with dd>d and dd <=d+TT[f,fl]-1 : z[f,pp,dd,ffll,t,k] <=1;
