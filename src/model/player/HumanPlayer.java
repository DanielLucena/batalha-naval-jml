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
    /*@
      requires name != null;
      requires fleet != null;
      requires fleet.size() <= 10000;
      requires (\forall int i; 0 <= i && i < fleet.size(); fleet.get(i) != null && fleet.get(i).length >= 0 && fleet.get(i).length <= 10000);
      ensures getName().equals(name);
      ensures getBoard() != null;
      ensures getFleet() == fleet;
    @*/
    public HumanPlayer(String name, List<Ship> fleet) {
        super(name, fleet);
        positionFleet();
    }

    /* Posiciona a frota do jogador humano no tabuleiro. */
    /*@ also
      ensures getBoard() != null;
      assignable System.out.outputText, System.out.eol;
    @*/
    @Override
    public void positionFleet() {
        System.out.printf("Do you want to position your fleet randomly, %s? (y or n): ", getName());
        String answer = sc.nextLine();
        boolean randomPositioning = answer.equalsIgnoreCase("y");

        for (Ship ship : getFleet()) {
            if (ship instanceof Submarine) {
                if (randomPositioning) {
                    placeSubmarineAutomatically();
                } else {
                    placeSubmarineManually();
                }
            }
        }
        getBoard().showBoard();
    }

    /* Posiciona submarinos automaticamente no tabuleiro. */
    /*@
      ensures getBoard() != null;
      assignable System.out.outputText, System.out.eol;
    @*/
    private void placeSubmarineAutomatically() {
        Random random = new Random();
        while (true) {
            String shipSpot = Fields.getRowLetter(random.nextInt(10) + 1) + (random.nextInt(10) + 1);
            try {
                getBoard().placeShip(shipSpot);
                break;
            } catch (Exception ignored) {}
        }
    }

    /* Posiciona submarinos manualmente no tabuleiro. */
    /*@
      ensures getBoard() != null;
      assignable System.out.outputText, System.out.eol;
    @*/
    private void placeSubmarineManually() {
        while (true) {
            System.out.print("Choose a spot to place a submarine (eg. B2): ");
            String shipSpot = sc.nextLine();
            try {
                getBoard().placeShip(shipSpot.toUpperCase());
                break;
            } catch (Exception e) {
                System.out.println(e.getMessage());
            }
        }
    }

    /* Realiza um disparo no tabuleiro do oponente. */
    /*@ also
      requires opponentBoard != null;
      ensures (\old(opponentBoard.getScore()) < opponentBoard.getScore());
      assignable System.out.outputText, System.out.eol;
    @*/
    @Override
    public void shoot(Board opponentBoard) {
        while (true) {
            System.out.print("Choose a spot to shoot (eg. B2): ");
            String shotSpot = sc.nextLine();
            try {
                getBoard().placeShot(shotSpot.toUpperCase(), opponentBoard);
                break;
            } catch (Exception e) {
                System.out.println(e.getMessage());
            }
        }
    }
}
