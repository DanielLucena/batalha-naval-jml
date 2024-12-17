package model;

public class Coordinate {

    private /*@ spec_public @*/ final String coordinateText;


    private /*@ spec_public @*/ int column;


    private /*@ spec_public @*/  int row;

    //@ public invariant 0 <= column <= 9;
    //@ public invariant 0 <= row <= 9;


    //@ ensures this.coordinateText.length() == 2;
    //@ signals_only Exception;
    public Coordinate(String coordinateText) throws Exception {
        try{
            this.coordinateText = coordinateText.substring(0,2);
            this.column = columnCharToInt(coordinateText.charAt(1));
            this.row = rowCharToInt(coordinateText.charAt(0));
        } catch (RuntimeException e) {
            throw new Exception("Incorrect Board Coordinate");
        }
    }

    //@ requires 0 <= row <= 9;
    //@ requires 0 <= column <= 9;
    public Coordinate(int row, int column) {
        this.row = row;
        this.column = column;
        this.coordinateText = ((char) (row +'A')) + ("" + column);
    }

    //@ requires true;
    //@ ensures 0 <= \result <= 9;
    //@ signals (RuntimeException e) !((rowChar >= 'a' && rowChar <= 'j') || (rowChar >= 'A' && rowChar <= 'J'));
    private int rowCharToInt(char rowChar) {
        if(rowChar >= 'a' && rowChar <= 'j'){
            return rowChar - 'a';
        }
        else if(rowChar >= 'A' && rowChar <= 'J'){
            return rowChar - 'A';
        }
        else {
            throw new RuntimeException();
        }
    }

    //@ requires true;
    //@ ensures 0 <= \result <= 9;
    //@ signals (RuntimeException e)  colChar < '0' || colChar > '9';
    private int columnCharToInt(char colChar) {
        if(colChar >= '0' && colChar <= '9'){
            return colChar - '0';
        }
        else {
            throw new RuntimeException();
        }
    }

    //@ ensures 0 <= \result <= 99;
    //@ pure
    public int getArrayPosition(){
        return (row * 10) + column;
    }


    //@ ensures 0 <= \result <= 9;
    //@ pure
    public int getColumn() {
        return column;
    }

    //@ ensures 0 <= \result <= 9;
    //@ pure
    public int getRow() {
        return row;
    }

    public String getCoordinateText() {
        return coordinateText;
    }
}
