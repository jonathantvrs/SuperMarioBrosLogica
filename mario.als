enum EstadoMario {
    MarioBros,
    SuperMario,
    FireMario,
    MarioCapa,
    MarioMorto,
    MarioInvencivel
}

sig Mario {
	curState: EstadoMario,
	nextState:EstadoMario,
	contact: EntidadeJogo
}

abstract sig EntidadeJogo {}

abstract sig Item extends EntidadeJogo {}
sig Flor, Pena, Cogumelo, Estrela extends Item {}

sig Inimigo extends EntidadeJogo {}
sig Nada extends EntidadeJogo {}

pred init[m:Mario] {
	m.curState = MarioBros
	m.nextState = MarioBros
	m.contact = Nada
}

fact CauseOfDeath{
	all m:Mario |(m.nextState = MarioMorto) <=> (m.curState = MarioMorto or (m.curState = MarioBros and m.contact = Inimigo))
}

fact CantRevive {
	all m: Mario | m.curState = MarioMorto implies m.nextState = MarioMorto
}

fact ContactNothing {
	all m:Mario | (m.contact = Nada) implies (m.curState = m.nextState)
}

fact BackToSuper{
	all m:Mario |   ((m.curState = FireMario or m.curState = MarioCapa) and m.contact = Inimigo) implies m.nextState = SuperMario
}

fact GetStar{
	all m:Mario |  (m.curState != MarioMorto and m.contact = Estrela) implies m.nextState = MarioInvencivel
}
fact GetFlower{
	all m:Mario |  (m.curState != MarioMorto and m.contact = Flor) implies m.nextState = FireMario
}
fact GetFeather{
	all m:Mario |  (m.curState != MarioMorto and m.contact = Pena) implies m.nextState = MarioCapa
}


//Mario Bros
fact GetMushroom{
	all m:Mario | (m.curState = MarioBros and m.contact = Cogumelo) implies m.nextState = SuperMario
}

//Super Mario
fact SuperContactWithEnemy{
	all m:Mario |  (m.curState = SuperMario and m.contact = Inimigo) implies m.nextState = MarioBros
}

fact SuperContactWithEnemyMushroom{
	all m:Mario |  (m.curState = SuperMario and m.contact = Cogumelo) implies m.nextState = SuperMario
}

//Fire Mario
fact StayFire{
	all m:Mario | (m.curState = FireMario and (m.contact = Cogumelo or m.contact = Flor)) implies m.nextState = FireMario
}

//Mario Capa
fact CapeChanges{
	all m:Mario | (m.curState = MarioCapa and (m.contact = Cogumelo or m.contact = Pena)) implies m.nextState = MarioCapa
}

//Mario Invencível
fact KeepsInvencible{
	all m:Mario | (m.curState = MarioInvencivel and (m.contact = Inimigo or m.contact = Cogumelo or m.contact = Estrela)) implies m.nextState = MarioInvencivel
}

fact InvencibleChanges{
	all m:Mario | (m.curState = MarioInvencivel and (m.contact != Pena and m.contact != Flor)) implies m.nextState = MarioInvencivel
}

// Predicados

pred ContactWithShroom[m:Mario] {
	m.contact = Cogumelo
	m.nextState = SuperMario
}

pred ContactWithFlower[m:Mario] {
	m.contact = Flor
	m.nextState = FireMario
}

pred ContactWithFeather[m:Mario] {
	m.curState != MarioMorto
	m.contact = Pena
	m.nextState = MarioCapa
}

pred ContactWithStar[m:Mario] {
	m.contact = Estrela
	m.nextState = MarioInvencivel
}

pred ContactWithShroomAndDontChange[m:Mario] {
	m.curState = FireMario or m.curState = SuperMario or m.curState = MarioCapa or m.curState = MarioInvencivel
	m.contact = Cogumelo
	m.nextState = m.curState
}

//TESTES

pred testKeepsStarMario [] {
	all m:Mario | m.contact = Estrela implies (m.nextState != MarioCapa and m.nextState != FireMario and m.nextState != SuperMario and m.nextState != MarioBros)
}

pred testKeepsFire[]{
	all m:Mario | (m.curState = FireMario and (m.contact = Flor or m.contact = Cogumelo)) implies m.nextState = FireMario
}

pred testKeepsCape [] {
	all m:Mario | (m.contact = Pena and m.curState != MarioMorto) implies (m.nextState != MarioInvencivel and m.nextState != MarioBros and m.nextState != FireMario and m.nextState != SuperMario)
}

pred testKeepsShroomMario[] {
	all m:Mario | (m.curState = FireMario or m.curState = SuperMario or m.curState = MarioCapa or m.curState = MarioInvencivel and m.contact = Cogumelo) implies m.nextState = m.curState
}

assert testEverything {
	testKeepsShroomMario and
	testKeepsStarMario and
	testKeepsCape and
	testKeepsFire
}

pred show [] {
}

run show for 5
