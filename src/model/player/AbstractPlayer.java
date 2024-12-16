package model.player;

import model.Board;
import model.Ship;

import java.util.List;

public abstract class AbstractPlayer implements Player {
    private final String name;
    private final Board board;
    private final List<Ship> fleet;

    /*@ invariant board != null; */
    /*@ invariant name != null; */
    /*@ invariant fleet != null; */

    /*@ ensures getName().equals(name); */
    /*@ ensures getBoard() != null; */
    public AbstractPlayer(String name, List<Ship> fleet) {
        this.name = name;
        this.fleet = fleet;
        this.board = new Board(name, getHitsToWin(fleet));
    }

    /*@ requires fleet != null; */
    /*@ ensures \result >= 0; */
    /*@ pure @*/
    private int getHitsToWin(List<Ship> fleet) {
        return fleet.stream().mapToInt(ship -> ship.length).sum();
    }

    /*@ also */
    /*@ ensures \result.equals(name); */
    @Override
    public String getName() {
        return name;
    }

    /*@ also */
    /*@ ensures \result == board; */
    @Override
    public Board getBoard() {
        return board;
    }

    /*@ ensures \result != null; */
    /*@ pure @*/
    public List<Ship> getFleet() {
        return fleet;
    }

    /*@ also */
    /*@ ensures getBoard() != null; */
    @Override
    public void resetPlayer() {
        board.fillBoard();
        positionFleet();
    }
}
