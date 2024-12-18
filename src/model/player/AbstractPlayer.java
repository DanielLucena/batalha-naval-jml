package model.player;

import model.Board;
import model.Ship;
import java.util.List;

public abstract class AbstractPlayer implements Player {
    /*@ spec_public @*/ protected final String name;
    /*@ spec_public @*/ private final Board board;
    /*@ spec_public @*/ private final List<Ship> fleet;

    /*@ public invariant name != null; */
    /*@ public invariant fleet != null; */

    /*@
      requires name != null;
      requires fleet != null;
      requires fleet.size() <= 10000;
      requires (\forall int i; 0 <= i && i < fleet.size(); fleet.get(i) != null && fleet.get(i).length >= 0 && fleet.get(i).length <= 10000);
      ensures getName().equals(name);
      ensures getBoard() != null;
      ensures getFleet() == fleet;
    @*/
    public AbstractPlayer(String name, List<Ship> fleet) {
        this.name = name;
        this.fleet = fleet;
        //@ assume (\forall int i; 0 <= i && i < fleet.size(); fleet.get(i) != null && fleet.get(i).length >= 0 && fleet.get(i).length <= 10000);
        int hits = getHitsToWin(fleet);
        this.board = new Board(name, hits);
    }


    /*@
    requires fleet != null;
    requires fleet.size() <= 10000;
    requires (\forall int i; 0 <= i && i < fleet.size(); fleet.get(i) != null && fleet.get(i).length >= 0 && fleet.get(i).length <= 10000);
    pure
    @*/
    private int getHitsToWin(List<Ship> fleet) {
        int sum = 0;
        //@ assert fleet.size() <= 10000;
        //@ assert (\forall int i; 0 <= i && i < fleet.size(); fleet.get(i) != null && fleet.get(i).length >= 0 && fleet.get(i).length <= 10000);

        /*@
        loop_invariant 0 <= j && j <= fleet.size();
        loop_invariant (\forall int k; 0 <= k && k < j; fleet.get(k) != null && fleet.get(k).length >= 0 && fleet.get(k).length <= 10000);
        loop_invariant 0 <= sum && sum <= 100000000;
        decreases fleet.size() - j;
        @*/
        for (int j = 0; j < fleet.size(); j++) {
            //@ assume sum + fleet.get(j).getLength() <= 100000000;
            sum = sum + fleet.get(j).getLength();
        }
        return sum;
    }


    /*@ also
      ensures \result != null;
      pure
    @*/
    @Override
    public String getName() {
        return name;
    }

    /*@ also
      ensures \result == board;
      ensures \result != null;
      pure
    @*/
    @Override
    public Board getBoard() {
        return board;
    }

    /*@
      ensures \result != null;
      pure
    @*/
    public List<Ship> getFleet() {
        return fleet;
    }

    /*@ also
      ensures getBoard() != null;
    @*/
    @Override
    public void resetPlayer() {
        board.fillBoard();
        positionFleet();
    }
}
