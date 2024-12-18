package model;

import java.util.Arrays;
import java.io.IOException;

public class Board {

    //@ spec_public
    private final char[] board = new char[100];

    //@ spec_public
    private final int hitsToWin;

    //@ spec_public
    private final String playerName;

    //@ public invariant board.length == 100;
    //@ public invariant 0 <= hitsToWin <= 10;

    // openjml -cp ./src --method Board --esc src/model/Board.java
    //@ ensures \forall int k; 0 <= k < board.length; board[k] == ' ';
    public Board (String playerName, int hitsToWin) {
        fillBoard();
        this.playerName = playerName;
        this.hitsToWin = hitsToWin;
    }

    // openjml -cp ./src --method showBoard --esc src/model/Board.java
    //@ assignable System.out.outputText, System.out.eol;
    public void showBoard() {
        showBoardHeader();
        System.out.print("  ");
        //@ loop_invariant 0 <= i <= 10;
        //@ decreases 10 - i;
        //@ loop_writes System.out.outputText
        for (int i = 0; i < 10 ; i++) {
            System.out.print(i + " ");
        }

        //@ loop_invariant 0 <= i <= board.length;
        //@ decreases board.length - i;
        //@ loop_writes System.out.outputText
        for (int i=0; i < board.length; i++) {
            if(i % 10 == 0){
                System.out.print("\n" + (char) ((i/10) + 'A') + " ");
            }
            System.out.print(board[i] + " ");
        }
        System.out.println();
    }

    // openjml -cp ./src --method showScore --esc src/model/Board.java
    //@ assignable System.out.outputText, System.out.eol;
    public void showScore(String enemyName){
        String scoreText = "Remaining " + enemyName + " ships : " + (hitsToWin - checkShipsCount());
        String emptySpacesBefore = " ".repeat((43 - scoreText.length()) / 2);
        String emptySpacesAfter = scoreText.length() % 2 == 0 ? emptySpacesBefore + " " : emptySpacesBefore;
        System.out.println("---------------------------------------------");
        System.out.println("|" + emptySpacesBefore + scoreText.toUpperCase() + emptySpacesAfter + "|");
        System.out.println("---------------------------------------------");
    }

    // openjml -cp ./src --method placeShip --esc src/model/Board.java
    //@ requires hasShipInSpot(coordinate);
    //@ signals_only Exception;
    //@ also
    //@ requires !hasShipInSpot(coordinate);
    //@ assigns this.board[*];
    public void placeShip (Coordinate coordinate) throws Exception {
        //Coordinate coordinate = new Coordinate(shipSpot);
        if (hasShipInSpot(coordinate)) throw new Exception("Unavailable Board Coordinate");
        this.board[coordinate.getArrayPosition()] = 'N';
    }

    // openjml -cp ./src --method hasShipInSpot --esc src/model/Board.java
    //@ requires coordinate != null;
    //@ pure
    private /*@ spec_public @*/ boolean hasShipInSpot (Coordinate coordinate) {
        return board[coordinate.getArrayPosition()] == 'N' || board[coordinate.getArrayPosition()] == 'n';
    }

    // openjml -cp ./src --method placeShot --esc src/model/Board.java
    //@ requires coordinate != null;
    //@ assignable System.out.outputText, System.out.eol, board[*], opponentBoard.board[*];
    //@ signals_only Exception;
    public void placeShot (Coordinate coordinate, Board opponentBoard) throws Exception {

        if (board[coordinate.getArrayPosition()] != ' ' &&
            board[coordinate.getArrayPosition()] != 'N') throw new Exception("Already shot at this spot");
        boolean shotHit = opponentBoard.getOpponentShot(coordinate.getArrayPosition());
        if (shotHit) System.out.printf("%s hit an Enemy Ship%n", playerName);
        markOwnBoard(coordinate.getArrayPosition(), shotHit);
    }


    //@ requires 0 <= position <= 99 && board[position] == ' ' && shotHit;
    //@ assigns board[position];
    //@ ensures board[position] == '*';
    //@ also
    //@ requires 0 <= position <= 99 && board[position] == ' ' && !shotHit;
    //@ assigns System.out.outputText, System.out.eol, board[position];
    //@ ensures board[position] == '-';
    //@ also
    //@ requires 0 <= position <= 99 && board[position] != ' ' && shotHit;
    //@ assigns board[position];
    //@ ensures board[position] == 'X';
    //@ also
    //@ requires 0 <= position <= 99 && board[position] != ' ' && !shotHit;
    //@ assigns System.out.outputText, System.out.eol, board[position];
    //@ ensures board[position] == 'n';
    private void markOwnBoard (int position, boolean shotHit) {
        if (board[position] == ' ') {
            if (shotHit) {
                board[position] = '*';
            }
            else {
                board[position] = '-';
                System.out.printf("%s shot in the water%n", playerName);
            }
        }
        else {
            if (shotHit) board[position] = 'X';
            else {
                board[position] = 'n';
                System.out.printf("%s shot in the water%n", playerName);
            }
        }
    }


    // openjml -cp ./src --method getOpponentShot --esc src/model/Board.java
    //@ requires 0 <= position <= 99 && (board[position] == 'N' || board[position] == 'X' || board[position] == 'n');
    //@ assigns board[position];
    //@ ensures \result == true;
    //@ also
    //@ requires 0 <= position <= 99 && !(board[position] == 'N' || board[position] == 'X' || board[position] == 'n');
    //@ assigns \nothing;
    //@ ensures \result == false;
    private boolean getOpponentShot(int position) {
        switch (board[position]) {
            case 'N':
                board[position] = ' ';
                return true;
            case 'X':
                board[position] = '*';
                return true;
            case 'n':
                board[position] = '-';
                return true;
            default:
                return false;
        }
    }


    //@ assignable board[*];
    public void fillBoard() {
        Arrays.fill(board, ' ');
    }


    //@ assignable System.out.outputText, System.out.eol;
    private void showBoardHeader () {
        String emptySpacesBefore = " ".repeat((43 - playerName.length()) / 2);
        String emptySpacesAfter = playerName.length() % 2 == 0 ? emptySpacesBefore + " " : emptySpacesBefore;
        System.out.println("---------------------------------------------");
        System.out.println("|" + emptySpacesBefore + playerName.toUpperCase() + emptySpacesAfter + "|");
        System.out.println("---------------------------------------------");
    }

    public boolean hasWon () {
        return checkShipsCount() == hitsToWin;
    }

    //@ ensures 0 <= \result <= 100;
    //@ pure
    private int checkShipsCount() {
        int hitsOnEnemyShips = 0;

        //@ loop_invariant 0 <= \count <= board.length;
        //@ loop_invariant 0 <= hitsOnEnemyShips <= \count;
        //@ loop_writes hitsOnEnemyShips;
        //@ decreases board.length - \count;
        for (char spot: board){
            if (spot == '*' || spot == 'X') hitsOnEnemyShips++;
        }
        return hitsOnEnemyShips;
    }

    /* Retorna a pontuação do tabuleiro com base nos acertos. */
    /*@ pure @*/
    public int getScore() {
        return checkShipsCount();
    }

    /*@
        ensures \result != null;
        pure
    @*/
    public char[] getBoardArray() {
        return board;
    }



}
