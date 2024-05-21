# Zhu 我们利用ProVerif工具进行安全仿真，验证了协议的安全性

type element. (*element in finite field or group*) (*定义一个环境*)
free Sec:channel [private].		(*secure channel*)
free Pub:channel.			(*public channel*)


(*-------Names & Variables-------*)
(*elements of cyclic group*)
const P:element.  (*生成元*)

(*1. KGC public key*)
free Ppub:element.

(*2 . KGC master secret key*)
free s:element [private].

(*3. RSUs' private key*)
(*RSUA*)
free xA:element [private].
free rA:element [private].
free dA:element [private].
(*RSUB*)
free xB:element [private].
free rB:element [private].
free dB:element [private].

(*4. RSUs' public parameters*)
(*RSUA*)
free XA:element.
free RA:element.
free IDA:bitstring.
(*RSUB*)
free XB:element.
free RB:element.
free IDB:bitstring.

(*5. Vehicles' private key*)
(*Vi*)
free xi:element [private].
free ri:element [private].
free di:element [private].
(*Vj*)
free xj:element [private].
free rj:element [private].
free dj:element [private].

(*6. Vehicles' public parameters*)
(*Vi*)
free Xi:element.
free Ri:element.
free PIDi:bitstring.
(*Vj*)
free Xj:element.
free Rj:element.
free PIDj:bitstring.

(*vehicle i & identity*)
free IDi:bitstring.
(*vehicle j & identity*)
free IDj:bitstring.

(*7. Vehicles' cross-domain communication credentical*)
free T3i:element [private].
free T3i':element [private].
free sigema_RVi:element [private].
free wi:bitstring [private].
free wi':bitstring [private].
free taui:element [private].

free T3j:element [private].
free T3j':element [private].
free sigema_RVj:element [private].
free wj:bitstring [private].
free wj':bitstring [private].
free tauj:element [private].

(*8. session key*)
free SKij:element [private].
free SKji:element [private].

(*9. else Parameters*)
free M01i:bitstring.
free M02i:bitstring.
free M03i:bitstring.
free M11i:bitstring.
free M12i:bitstring.
free M13i:bitstring.

(*-------Constructors, Destructors & Equations------*)
fun Xor(element,bitstring):bitstring.
fun Xor1(element,bitstring):bitstring.
fun Xor2(element,element):bitstring.
fun Xor3(element,bitstring):element.
fun H(element):element.
fun H0(element,element):element.
fun H1(element,bitstring,element,element):element.
fun H2(bitstring,bitstring,bitstring,bitstring,element,element,element,element):element.
fun H3(bitstring,bitstring,bitstring,bitstring,element,element,element,element):element.
fun H2'(bitstring,element,element,element):element.
fun H3'(bitstring,element,element,element):element.
fun H4(element,bitstring,element,element,element,element):element.
fun H5(element,bitstring,element,element,element,element):element.
fun H6(bitstring,bitstring,element,element):element.
fun H7(element,element,bitstring):element.
fun H8(bitstring,bitstring,element,element):bitstring.

fun Pairing(element,element):element.  (*Pairing operation:e(g,g)*)
fun Mult(element,element):element.  (*Multiplication in group: G×G*)
fun Add(element,element):element.	 (*Addition*)
fun Powzn(element,element):element. 	(*g^s:Powzn(g,s)*)


(*Event*)
event beginVehiclei(bitstring).
event endVehiclei(bitstring).
event beginVehiclej(bitstring).
event endVehiclej(bitstring).

(*Queries*)
query attacker(xi).
query attacker(di).
query attacker(xj).
query attacker(dj).
query attacker(SKij).(*通过这些询问验证会话密钥的安全性*)
query attacker(SKji).
query ID:bitstring; inj-event (endVehiclei(IDi)) ==> inj-event(beginVehiclei(IDi)).(*签名的不可伪造性；这两行语句不可以改*)
query ID:bitstring; inj-event (endVehiclej(IDj)) ==> inj-event(beginVehiclej(IDj)).


(*Processes*)

(*KGC Processes*)
let VehicleiReg=
	in(Sec,(IDi:bitstring,Xi:element)); (*in：输入*)
	
	let Ri = Powzn(P,ri) in        (*每个运算let开始 in结束*)
	let PIDi=Xor(H0(s,Ri),IDi) in
	let di=Add(ri,Mult(s,H1(Ppub,PIDi,Xi,Ri))) in
	0.
let VehiclejReg=
	in(Sec,(IDj:bitstring,Xj:element));
	let Rj = Powzn(P,rj) in
	let PIDj=Xor(H0(s,Rj),IDj) in
	let dj=Add(rj,Mult(s,H1(Ppub,PIDj,Xj,Rj))) in
	0.
let RSUAReg=
	in(Sec,(IDA:bitstring,XA:element)); 
	let RA = Powzn(P,rA) in 
	let dA=Add(rA,Mult(s,H1(Ppub,IDA,XA,RA))) in
	0.
let RSUBReg=
	in(Sec,(IDb:bitstring,XB:element)); 
	let RB = Powzn(P,rB) in 
	let dB=Add(rB,Mult(s,H1(Ppub,IDB,XB,RB))) in
	0.
let KGC=VehicleiReg | VehiclejReg | RSUAReg | RSUBReg.

(*Vehicle Processes*)
(*Vi Processes*)
let Vehiclei=
	(*Registration*)
	let Xi = Powzn(P,xi) in 
	out(Sec,(IDi,Xi));
	
	(*V&RSU Authentication*)
	(*new t0i,t1i,T0i,T1i,Q0i,M0.1i,M0.2i,M0.3i,sigmai,Gamma1i:element;*)
	new t0i:element;
	new t1i:element;
	new T0i:element;
	new T1i:element;
	let T0i = Powzn(P,t0i) in 
	let T1i = Powzn(P,t1i) in
	let Q0i = Mult(t0i,Add(Add(XA,RA),Mult(Ppub,H1(Ppub,IDA,XA,RA)))) in
	let M01i = Xor1(H(Q0i),PIDi) in
	let M02i = Xor2(H(Q0i),T0i) in
	let M03i = Xor2(H(Q0i),T1i) in
	new sigmai:element;
	new Gamma1i:element;
	let sigmai = Add(t1i,Add(Mult(H2(PIDi,M01i,M02i,M03i,Xi,Ri,T1i,Gamma1i),xi),Mult(H3(PIDi,M01i,M02i,M03i,Xi,Ri,T1i,Gamma1i),di))) in
	out(Sec,(M01i,M02i,M03i,sigmai,T0i,Gamma1i));
	
	in(Sec,(M11i:bitstring,M12i:bitstring,M13i:bitstring,sigma_RVi:element,T2i:element,Gamma2i:element));
	new Q1i':element;
	let Q1i' = Mult(T2i,Add(xi,di)) in
	let wi' = Xor1(H(Q1i'),M11i) in
	let T3i' = Xor3(H(Q1i'),M13i) in
	if(Powzn(P,sigma_RVi)= Add(Add(T3i',Mult(H2'(wi,XA,RA,T3i'),XA)),Mult(H3'(wi,XA,RA,T3i'),Add(RA,Mult(Ppub,H1(Ppub,IDA,XA,RA)))))) then
	let taui = H7(T3i',sigma_RVi,wi') in
	
	(*Cross-domain Authentication and Key Agreement*)
	event beginVehiclei(IDi);  (*事件开始*)

	(*new ti,tA,Ti,Pi,sigma_Vi,Gamma3i:element;*)
	new ti:element;
	new tA:element;
	let Ti = Powzn(P,ti) in 
	let Pi = Powzn(P,tA) in
	new sigma_Vi:element;
	new Gamma3i:element;
	let sigma_Vi = Add(Add(sigema_RVi,ti),Add(Mult(H4(Ppub,PIDi,Xi,Ri,Ti,Gamma3i),xi),Mult(H5(Ppub,PIDi,Xi,Ri,Ti,Gamma3i),di))) in
    out(Pub,(T3i',wi',sigma_Vi,Ti,Pi,Gamma3i));
	in(Pub,(T3j':element,wj':bitstring,sigma_Vj:element,Tj:element,Pj:element,Gamma4j:element));
	if(Powzn(P,sigma_Vj)=  Add(   Add(Add(T3j',Mult(H2'(wj',XB,RB,T3j'),XB)),Mult(H3'(wj',XB,RB,T3j'),Add(RB,Mult(Ppub,H1(Ppub,IDB,XB,RB))))) , Add(Add(Tj,Mult(H4(Ppub,PIDj,Xj,Rj,Tj,Gamma4j),Xj)),Mult(H5(Ppub,PIDj,Xj,Rj,Tj,Gamma4j),Add(Rj,Mult(Ppub,H1(Ppub,IDj,Xj,Rj)))))   )) then
	let SKij = H6(PIDi,PIDj,Mult(tA,Pj),Mult(Add(xi,di),Add(Add(Xj,Rj),Mult(Ppub,H1(Ppub,PIDj,Xj,Rj))))) in
	event endVehiclei(IDi)
	else 0.
	
(*Vj Processes*)
let Vehiclej=
	(*Registration*)
	let Xj = Powzn(P,xj) in 
	out(Sec,(IDj,Xj));
	
	(*V&RSU Authentication*)
	(*new t0j,t1j,T0j,T1j,Q0j,M0.1j,M0.2j,M0.3j,sigmaj,Gamma1j:element;*)
	new t0j:element;
	new t1j:element;
	new T0j:element;
	new T1j:element;
	let T0j = Powzn(P,t0j) in 
	let T1j = Powzn(P,t1j) in
	let Q0j = Mult(t0j,Add(Add(XB,RB),Mult(Ppub,H1(Ppub,IDB,XB,RB)))) in
	let M01j = Xor1(H(Q0j),PIDj) in
	let M02j = Xor2(H(Q0j),T0j) in
	let M03j = Xor2(H(Q0j),T1j) in
	new sigmaj:element;
	new Gamma1j:element;
	let sigmaj = Add(t1j,Add(Mult(H2(PIDj,M01j,M02j,M03j,Xj,Rj,T1j,Gamma1j),xj),Mult(H3(PIDj,M01j,M02j,M03j,Xj,Rj,T1j,Gamma1j),dj))) in  (* M0！ *)
	out(Sec,(M01j,M02j,M03j,sigmaj,T0j,Gamma1j));
	
	in(Sec,(M11j:bitstring,M12j:bitstring,M13j:bitstring,sigma_RVj:element,T2j:element,Gamma2j:element));
	new Q1j':element;
	let Q1j' = Mult(T2j,Add(xj,dj)) in
	let wj' = Xor1(H(Q1j'),M11j) in
	let T3j' = Xor3(H(Q1j'),M13j) in
	if(Powzn(P,sigma_RVj)= Add(Add(T3j',Mult(H2'(wj,XB,RB,T3j),XB)),Mult(H3'(wj,XB,RB,T3j),Add(RB,Mult(Ppub,H1(Ppub,IDB,XB,RB)))))) then
	let tauj = H7(T3j',sigma_RVj,wj') in
	
	(*Cross-domain Authentication and Key Agreement*)
	event beginVehiclej(IDj); (*事件开始*)
	in(Pub,(T3i':element,wi':bitstring,sigma_Vi:element,Ti:element,Pi:element,Gamma3i:element));
	if(Powzn(P,sigma_Vi)=  Add(   Add(Add(T3i',Mult(H2'(wi',XA,RA,T3i'),XA)),Mult(H3'(wi',XA,RA,T3i'),Add(RA,Mult(Ppub,H1(Ppub,IDA,XA,RA))))) , Add(Add(Ti,Mult(H4(Ppub,PIDi,Xi,Ri,Ti,Gamma3i),Xi)),Mult(H5(Ppub,PIDi,Xi,Ri,Ti,Gamma3i),Add(Ri,Mult(Ppub,H1(Ppub,IDi,Xi,Ri)))))   )) then
	(*new tj,tB,Tj,Pj,sigma_Vj,Gamma4j:element;*)
	new tj:element;
	new tB:element;
	let Tj = Powzn(P,tj) in 
	let Pj = Powzn(P,tB) in
	new sigma_Vj:element;
	new Gamma4j:element;
	let sigma_Vj = Add(Add(sigema_RVj,tj),Add(Mult(H4(Ppub,PIDj,Xj,Rj,Tj,Gamma4j),xj),Mult(H5(Ppub,PIDj,Xj,Rj,Tj,Gamma4j),dj))) in
	let SKji = H6(PIDi,PIDj,Mult(tB,Pi),Mult(Add(xj,dj),Add(Add(Xi,Ri),Mult(Ppub,H1(Ppub,PIDi,Xi,Ri))))) in
	out(Pub,(T3j',wj',sigma_Vj,Tj,Pj,Gamma4j));
	event endVehiclej(IDj)
	else 0.

(*RSU Processes*)
(*RSUA Processes*)
let RSUA=
	(*Registration*)
	let XA = Powzn(P,xA) in 
	out(Sec,(IDA,XA));
	
	(*V&RSU Authentication*)
	in(Sec,(M01i:bitstring,M02i:bitstring,M03i:bitstring,sigmai:element,T0i:element,Gamma1i:element));
	new Q0i':element;
	let Q0i' = Mult(T0i,Add(xA,dA)) in
	new T1i':element;
	let T1i' = Xor3(H(Q0i'),M03i) in
	if(Powzn(P,sigmai)= Add(Add(T1i',Mult(H2(PIDi,M01i,M02i,M03i,Xi,Ri,T1i',Gamma1i),Xi)),Mult(H3(PIDi,M01i,M02i,M03i,Xi,Ri,T1i',Gamma1i),Add(Ri,Mult(Ppub,H1(Ppub,PIDi,Xi,Ri)))))) then
	(*new t2i,t3i,T2i,T3i,Q1i,M1.1i,M1.2i,M1.3i,Gamma2i:element;*)
	new t2i:element;
	new t3i:element;
	new T2i:element;
	new T3i:element;
	let T2i = Powzn(P,t2i) in 
	let T3i = Powzn(P,t3i) in
	let Q1i = Mult(t2i,Add(Add(Xi,Ri),Mult(Ppub,H1(Ppub,PIDi,Xi,Ri)))) in
	new Di:element;
	new Texti:element;
	let wi = H8(IDA,PIDi,Di,Texti) in
	let M11i = Xor1(H(Q1i),wi) in
	let M12i = Xor2(H(Q1i),T2i) in
	let M13i = Xor2(H(Q1i),T3i) in
	new sigema_RVi:element;
	new Gamma2i:element;
	let sigma_RVi = Add(t3i,Add(Mult(H2'(wi,XA,RA,T3i),xA),Mult(H3'(wi,XA,RA,T3i),dA))) in
	out(Sec,(M11i,M12i,M13i,sigma_RVi,T2i,Gamma2i));
	0.
(*RSUB Processes*)
let RSUB=
	(*Registration*)
	let XB= Powzn(P,xB) in 
	out(Sec,(IDB,XB));
	
	(*V&RSU Authentication*)
	in(Sec,(M01j:bitstring,M02j:bitstring,M03j:bitstring,sigmaj:element,T0j:element,Gamma1j:element));
	new Q0j':element;
	let Q0j' = Mult(T0j,Add(xB,dB)) in
	let T1j' = Xor3(H(Q0j'),M03j) in
	if(Powzn(P,sigmaj)= Add(Add(T1j',Mult(H2(PIDj,M01j,M02j,M03j,Xj,Rj,T1j',Gamma1j),Xj)),Mult(H3(PIDj,M01j,M02j,M03j,Xj,Rj,T1j',Gamma1j),Add(Rj,Mult(Ppub,H1(Ppub,PIDj,Xj,Rj)))))) then
	(*new t2j,t3j,T2j,T3j,Q1j,M1.1j,M1.2j,M1.3j,Gamma2j:element;*)
	new t2j:element;
	new t3j:element;
	new T2j:element;
	new T3j:element;
	let T2j = Powzn(P,t2j) in 
	let T3j = Powzn(P,t3j) in
	let Q1j = Mult(t2j,Add(Add(Xj,Rj),Mult(Ppub,H1(Ppub,PIDj,Xj,Rj)))) in
	new Dj:element;
	new Textj:element;
	let wj = H8(IDB,PIDj,Dj,Textj) in
	let M11j = Xor1(H(Q1j),wj) in
	let M12j = Xor2(H(Q1j),T2j) in
	let M13j = Xor2(H(Q1j),T3j) in
	new sigema_RVj:element;
	new Gamma2j:element;
	let sigma_RVj = Add(t3j,Add(Mult(H2'(wj,XB,RB,T3j),xB),Mult(H3'(wj,XB,RB,T3j),dB))) in
	out(Sec,(M11j,M12j,M13j,sigma_RVj,T2j,Gamma2j));
	0.
	
	(*Processes Replication*)
	process 
    (!Vehiclei | !Vehiclej | !KGC)
