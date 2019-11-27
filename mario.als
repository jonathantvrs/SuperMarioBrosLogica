enum EstadoMario {
    MarioPequeno,		-- Mario Bros
    MarioGrande,		-- Super Mario 
    MarioPoderDeFogo,	-- Fire Mario
    MarioPoderDeVoo,	-- Cape Mario
    MarioInvencivel,			-- Invencible Mario
    MarioMorto			-- Dead Mario
}

sig Mario {
	curState: EstadoMario,
	nextState:EstadoMario,
	contact: Iteracao
}

abstract sig Iteracao {}

sig Flor, Pena, Cogumelo, Estrela, Inimigo, NIL extends Iteracao {}

-- Estado inicial
pred init[m:Mario] { 				
	m.curState = MarioPequeno
	m.nextState = MarioPequeno
	m.contact = NIL
}

-- Cada item está ligado a um único Mario 
fact oneItemToOneMario{
	all i:Iteracao |
		one i.~contact 
}

fact CauseOfDeath{
	all m:Mario |
		(m.nextState = MarioMorto) <=> (m.curState = MarioMorto or (m.curState = MarioPequeno and m.contact = Inimigo))
}

fact CantRevive {
	all m: Mario |
		m.curState = MarioMorto 
		implies m.nextState = MarioMorto
}

fact ContactNothing {
	all m:Mario |
		(m.contact = NIL) 
		implies (m.curState = m.nextState)
}

fact BackToSuper{
	all m:Mario |
		((m.curState = MarioPoderDeFogo or m.curState = MarioPoderDeVoo) and m.contact = Inimigo) 
		implies m.nextState = MarioGrande
}

fact GetStar{
	all m:Mario |
		(m.curState != MarioMorto and m.contact = Estrela) 
		implies m.nextState = MarioInvencivel
}
fact GetFlower{
	all m:Mario |
		(m.curState != MarioMorto and m.contact = Flor) 
		implies m.nextState = MarioPoderDeFogo
}
fact GetFeather{
	all m:Mario |
		(m.curState != MarioMorto and m.contact = Pena) 
		implies m.nextState = MarioPoderDeVoo
}


//Mario Bros
fact GetMushroom{
	all m:Mario |
		(m.curState = MarioPequeno and m.contact = Cogumelo) 
		implies m.nextState = MarioGrande
}

//Super Mario
fact SuperContactWithEnemy{
	all m:Mario |
		(m.curState = MarioGrande and m.contact = Inimigo) 
		implies m.nextState = MarioPequeno
}

fact SuperContactWithMushroom{
	all m:Mario |
		(m.curState = MarioGrande and m.contact = Cogumelo) 
		implies m.nextState = MarioGrande
}

//Fire Mario
fact StayFire{
	all m:Mario |
		(m.curState = MarioPoderDeFogo and (m.contact = Cogumelo or m.contact = Flor)) 
		implies m.nextState = MarioPoderDeFogo
}

//Mario Capa
fact CapeChanges{
	all m:Mario |
		(m.curState = MarioPoderDeVoo and (m.contact = Cogumelo or m.contact = Pena)) 
		implies m.nextState = MarioPoderDeVoo
}

//Mario Invencível
fact KeepsInvencible{
	all m:Mario |
		(m.curState = MarioInvencivel and (m.contact = Inimigo or m.contact = Cogumelo or m.contact = Estrela)) 
		implies m.nextState = MarioInvencivel
}

fact InvencibleChanges{
	all m:Mario |
		(m.curState = MarioInvencivel and (m.contact != Pena and m.contact != Flor)) 
		implies m.nextState = MarioInvencivel
}

// Predicados

pred ContactWithShroom[m:Mario] {
	m.contact = Cogumelo
	m.nextState = MarioGrande
}

pred ContactWithFlower[m:Mario] {
	m.contact = Flor
	m.nextState = MarioPoderDeFogo
}

pred ContactWithFeather[m:Mario] {
	m.curState != MarioMorto
	m.contact = Pena
	m.nextState = MarioPoderDeVoo
}

pred ContactWithStar[m:Mario] {
	m.contact = Estrela
	m.nextState = MarioInvencivel
}

pred ContactWithShroomAndDontChange[m:Mario] {
	m.curState = MarioPoderDeFogo or m.curState = MarioGrande or m.curState = MarioPoderDeVoo or m.curState = MarioInvencivel
	m.contact = Cogumelo
	m.nextState = m.curState
}

//TESTES

pred testeMarioColetaCogumeloENaoMuda[] {
	all m:Mario |
		((m.curState = MarioPoderDeFogo or m.curState = MarioGrande or m.curState = MarioPoderDeVoo or m.curState = MarioInvencivel) and m.contact = Cogumelo) 
		implies m.nextState = m.curState
}

pred testeMarioEstrelaConsistente [] {
	all m:Mario |
		m.contact = Estrela 
		implies (m.nextState != MarioPoderDeVoo and m.nextState != MarioPoderDeFogo and m.nextState != MarioGrande and m.nextState != MarioPequeno)
}

pred testeMarioCapaConsistente [] {
	all m:Mario |
		(m.contact = Pena and m.curState != MarioMorto) 
		implies (m.nextState != MarioInvencivel and m.nextState != MarioPequeno and m.nextState != MarioPoderDeFogo and m.nextState != MarioGrande)
}

pred testeFireMarioConsistente[]{
	all m:Mario |
		(m.curState = MarioPoderDeFogo and (m.contact = Flor or m.contact = Cogumelo)) 
		implies m.nextState = MarioPoderDeFogo
}



assert testeGeral {
	testeMarioColetaCogumeloENaoMuda and
	testeMarioEstrelaConsistente and
	testeMarioCapaConsistente and
	testeFireMarioConsistente
}

--check testeGeral

pred show [] {
}

run show for 5
