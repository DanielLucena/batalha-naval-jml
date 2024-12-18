package model.player;

import model.Board;
import model.Coordinate;
import model.Fields;
import model.Ship;
import java.util.List;
import java.util.Random;

public class ComputerPlayer extends AbstractPlayer {
    private final Random random = new Random();

    /* Construtor do jogador computador. */
    /*@
      requires fleet != null;
      requires fleet.size() <= 10000;
      requires (\forall int i; 0 <= i && i < fleet.size(); fleet.get(i) != null && fleet.get(i).length >= 0 && fleet.get(i).length <= 10000);
      ensures getName().equals("Computer");
      ensures getBoard() != null;
      ensures getFleet() == fleet;
    @*/
    public ComputerPlayer(List<Ship> fleet) {
        super("Computer", fleet);
        positionFleet();
    }

    /*@ also
      ensures getBoard() != null;
    @*/
    @Override
    public void positionFleet() {
        for (Ship ship : getFleet()) {
            if (ship instanceof model.Submarine) {
                placeSubmarineAutomatically();
            }
        }
    }

    /*@ ensures getBoard() != null; */
    private void placeSubmarineAutomatically() {
        while (true) {
            //String shipSpot = Fields.getRowLetter(random.nextInt(10) + 1) + (random.nextInt(10) + 1);
            try {
            Coordinate shipSpot = new Coordinate(random.nextInt(10), random.nextInt(10));
                getBoard().placeShip(shipSpot);
                break;
            } catch (Exception ignored) {}
        }
    }

    /*@ also
      requires opponentBoard != null;
    //   ensures (\old(opponentBoard.getScore()) < opponentBoard.getScore());
    @*/
    @Override
    public void shoot(Board opponentBoard) {
        while (true) {
            //String shotSpot = Fields.getRowLetter(random.nextInt(10) + 1) + (random.nextInt(10) + 1);
            try {
                Coordinate shotSpot = new Coordinate(random.nextInt(10), random.nextInt(10));
                getBoard().placeShot(shotSpot, opponentBoard);
                break;
            } catch (Exception ignored) {}
        }
    }
}