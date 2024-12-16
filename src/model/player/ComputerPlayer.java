package model.player;

import model.Board;
import model.Fields;
import model.Ship;

import java.util.List;
import java.util.Random;

public class ComputerPlayer extends AbstractPlayer {
    private final Random random = new Random();

    /* Construtor que inicializa o jogador computador. */
    /*@ ensures this.getName().equals("Computer"); */
    /*@ ensures this.getBoard() != null; */
    public ComputerPlayer(List<Ship> fleet) {
        super("Computer", fleet);
        positionFleet();
    }

    /* Posiciona automaticamente a frota no tabuleiro. */
    /*@ ensures getBoard() != null; */
    @Override
    public void positionFleet() {
        for (Ship ship : fleet) {
            if (ship instanceof model.Submarine) {
                placeSubmarineAutomatically();
            }
        }
    }

    /* Posiciona submarinos automaticamente no tabuleiro. */
    /*@ ensures (\forall int i, j; 1 <= i && i <= 10 && 1 <= j && j <= 10; board != null); */
    private void placeSubmarineAutomatically() {
        while (true) {
            String shipSpot = Fields.getRowLetter(random.nextInt(10) + 1) + (random.nextInt(10) + 1);
            try {
                board.placeShip(shipSpot);
                break;
            } catch (Exception ignored) {}
        }
    }

    /* Realiza um disparo no tabuleiro do oponente. */
    /*@ requires opponentBoard != null; */
    /*@ ensures (\old(opponentBoard.getScore()) < opponentBoard.getScore()); */
    @Override
    public void shoot(Board opponentBoard) {
        while (true) {
            String shotSpot = Fields.getRowLetter(random.nextInt(10) + 1) + (random.nextInt(10) + 1);
            try {
                board.placeShot(shotSpot, opponentBoard);
                break;
            } catch (Exception ignored) {}
        }
    }
}
