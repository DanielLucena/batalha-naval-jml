package model;

import java.util.Arrays;
import java.io.IOException;

public class Board {

    private final char[][] board = new char[11][11];
    private final int hitsToWin;
    private final String playerName;

    public Board (String playerName, int hitsToWin) {
        fillBoard();
        this.playerName = playerName;
        this.hitsToWin = hitsToWin;
    }

    public void showBoard() {
        showBoardHeader();
        for (char[] column : board) {
            System.out.print("| ");
            for (char row : column) {
                System.out.print(row + " | ");
            }
            System.out.println("\n---------------------------------------------");
        }
    }

    public void showScore(String enemyName){
        String scoreText = "Remaining " + enemyName + " ships : " + (hitsToWin - checkShipsCount());
        String emptySpacesBefore = " ".repeat((43 - scoreText.length()) / 2);
        String emptySpacesAfter = scoreText.length() % 2 == 0 ? emptySpacesBefore + " " : emptySpacesBefore;
        System.out.println("---------------------------------------------");
        System.out.println("|" + emptySpacesBefore + scoreText.toUpperCase() + emptySpacesAfter + "|");
        System.out.println("---------------------------------------------");
    }


    public void placeShip (String shipSpot) throws Exception {
        Coordinate coordinate = new Coordinate(shipSpot);
        int row = coordinate.getRow();
        int column = coordinate.getColumn();
        if (hasShipInSpot(row, column)) throw new Exception("Unavailable Board Coordinate");
        this.board[row][column] = 'N';
    }

    private boolean hasShipInSpot (int row, int column) {
        return board[row][column] == 'N' || board[row][column] == 'n';
    }

    public void placeShot (String shotCoordinate, Board opponentBoard) throws Exception {

        if (!playerName.toLowerCase().equals("computer")) clearScreen();

        Coordinate coordinate = new Coordinate(shotCoordinate);
        int rowNumber = coordinate.getRow();
        int column = coordinate.getColumn();
        if (board[rowNumber][column] != ' ' &&
            board[rowNumber][column] != 'N') throw new Exception("Already shot at this spot");
        boolean shotHit = opponentBoard.getOpponentShot(rowNumber, column);
        if (shotHit) System.out.printf("%s hit an Enemy Ship%n", playerName);
        if (board[rowNumber][column] == ' ') {
            if (shotHit) {
                board[rowNumber][column] = '*';
            }
            else {
                board[rowNumber][column] = '-';
                System.out.printf("%s shot in the water%n", playerName);
            }
        }
        else {
            if (shotHit) board[rowNumber][column] = 'X';
            else {
                board[rowNumber][column] = 'n';
                System.out.printf("%s shot in the water%n", playerName);
            }
        }
    }

    private boolean getOpponentShot (int rowNumber, int column) {
        if (board[rowNumber][column] == 'N') {
            board[rowNumber][column] = ' ';
            return true;
        }
        if (board[rowNumber][column] == 'X') {
            board[rowNumber][column] = '*';
            return true;
        }
        if (board[rowNumber][column] == 'n') {
            board[rowNumber][column] = '-';
            return true;
        }
        return false;
    }

    public void fillBoard () {
        for (char[] row : board) Arrays.fill(row, ' ');
        for (int i = 1; i < board[0].length; i++) {
            board[0][i] = Integer.toString(i - 1).charAt(0);

        }
        for (int i = 1; i < board.length; i++) {
            board[i][0] = (char) (i-1 + 'A');
        }
    }

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

    public void clearScreen () {
        try {
            if (System.getProperty("os.name").contains("Windows"))
                new ProcessBuilder("cmd", "/c", "cls").inheritIO().start().waitFor();
            else
                Runtime.getRuntime().exec("clear");
        } catch (IOException | InterruptedException ignored) {
        }
    }

    private int checkShipsCount (){
        int hitsOnEnemyShips = 0;
        for (int i = 1; i < board.length; i++) {
            for (int j = 1; j < board[i].length; j++) {
                if (board[i][j] == '*' || board[i][j] == 'X') hitsOnEnemyShips++;
            }
        }

        return hitsOnEnemyShips;
    }

}
