module mario

--assinaturas

sig mario {
	state: one mario_state
}

abstract sig mario_state {
}

sig pequeno, grande, fogo, capa, invencivel, morto extends mario_state{
}

--fatos

fact {

    --Só existe um mário
	#mario = 1

    -Só existe um estado para cada mário
	all ms: mario_state | one ms.~state 
	
    --TODO:
	--Todo mario começa pequeno
    --Um state para outro
	--Toma dano volta para mario pequeno
	--Apenas mario pequeno pode ir pra morto
}

pred show[]{
}

run show for 5
