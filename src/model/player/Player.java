package model.player;

import model.Board;

public interface Player {
    /* Retorna o nome do jogador. */
    /*@ ensures \result != null; */
    /*@ pure @*/
    String getName();

    /* Retorna o tabuleiro do jogador. */
    /*@ ensures \result != null; */
    /*@ pure @*/
    Board getBoard();

    /* Posiciona a frota do jogador no tabuleiro. */
    /*@ ensures true; */
    void positionFleet();

    /* Realiza um disparo no tabuleiro do oponente. */
    /*@ requires opponentBoard != null; */
    // /*@ ensures (\old(opponentBoard.getScore()) < opponentBoard.getScore()); */
    void shoot(Board opponentBoard);

    /* Restaura o estado inicial do jogador. */
    /*@ ensures true; */
    void resetPlayer();
}
