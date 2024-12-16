package model.player;

import model.Board;
import model.Fields;
import model.Ship;
import model.Submarine;

import java.util.List;
import java.util.Random;
import java.util.Scanner;

public class HumanPlayer extends AbstractPlayer {
    private final Scanner sc = new Scanner(System.in);

    /* Construtor que inicializa o jogador humano. */
    /*@ ensures this.getName().equals(name); */
    /*@ ensures this.getBoard() != null; */
    public HumanPlayer(String name, List<Ship> fleet) {
        super(name, fleet);
        positionFleet();
    }

    /* Posiciona a frota do jogador humano no tabuleiro. */
    /*@ ensures getBoard() != null; */
    @Override
    public void positionFleet() {
        System.out.printf("Do you want to position your fleet randomly, %s? (y or n): ", name);
        String answer = sc.nextLine();
        boolean randomPositioning = answer.equalsIgnoreCase("y");

        for (Ship ship : fleet) {
            if (ship instanceof Submarine) {
                if (randomPositioning) {
                    placeSubmarineAutomatically();
                } else {
                    placeSubmarineManually();
                }
            }
        }
        board.showBoard();
    }

    /* Posiciona submarinos automaticamente no tabuleiro. */
    /*@ ensures (\forall int i, j; 1 <= i && i <= 10 && 1 <= j && j <= 10; board != null); */
    private void placeSubmarineAutomatically() {
        Random random = new Random();
        while (true) {
            String shipSpot = Fields.getRowLetter(random.nextInt(10) + 1) + (random.nextInt(10) + 1);
            try {
                board.placeShip(shipSpot);
                break;
            } catch (Exception ignored) {}
        }
    }

    /* Posiciona submarinos manualmente no tabuleiro. */
    /*@ ensures (\forall int i, j; 1 <= i && i <= 10 && 1 <= j && j <= 10; board != null); */
    private void placeSubmarineManually() {
        while (true) {
            System.out.print("Choose a spot to place a submarine (eg. B2): ");
            String shipSpot = sc.nextLine();
            try {
                board.placeShip(shipSpot.toUpperCase());
                break;
            } catch (Exception e) {
                System.out.println(e.getMessage());
            }
        }
    }

    /* Realiza um disparo no tabuleiro do oponente. */
    /*@ requires opponentBoard != null; */
    /*@ ensures (\old(opponentBoard.getScore()) < opponentBoard.getScore()); */
    @Override
    public void shoot(Board opponentBoard) {
        while (true) {
            System.out.print("Choose a spot to shoot (eg. B2): ");
            String shotSpot = sc.nextLine();
            try {
                board.placeShot(shotSpot.toUpperCase(), opponentBoard);
                break;
            } catch (Exception e) {
                System.out.println(e.getMessage());
            }
        }
    }
}
