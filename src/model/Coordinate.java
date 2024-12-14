package model;

public class Coordinate {

    private /*@ spec_public @*/ final String coordinateText;


    private /*@ spec_public @*/ int column;


    private /*@ spec_public @*/  int row;


    //@ requires coordinateText.length() == 2;
    //@ requires '0' <= coordinateText.charAt(1) <= '9';
    //@ requires ((coordinateText.charAt(0) >= 'a' && coordinateText.charAt(0) <= 'j') || (coordinateText.charAt(0) >= 'A' && coordinateText.charAt(0) <= 'J'));
    //@ ensures this.coordinateText.length() == 2;
    //@ signals_only Exception;
    public Coordinate(String coordinateText) throws Exception {
        try{
            this.coordinateText = coordinateText.substring(0,2);
            this.column = columnCharToInt(coordinateText.charAt(1));
            this.row = rowCharToInt(coordinateText.charAt(0));
        } catch (RuntimeException e){
            throw new Exception("Incorrect Board Coordinate");
        }


    }

    //@ requires true;
    //@ ensures 1 <= \result <= 10;
    //@ signals (RuntimeException e) !((rowChar >= 'a' && rowChar <= 'j') || (rowChar >= 'A' && rowChar <= 'J'));
    private int rowCharToInt(char rowChar) {
        if(rowChar >= 'a' && rowChar <= 'j'){
            return rowChar - 'a' + 1;
        }
        else if(rowChar >= 'A' && rowChar <= 'J'){
            return rowChar - 'A' + 1;
        }
        else {
            throw new RuntimeException();
        }
    }

    //@ requires true;
    //@ ensures 1 <= \result <= 10;
    //@ signals (RuntimeException e)  colChar < '0' || colChar > '9';
    private int columnCharToInt(char colChar) {
        if(colChar >= '0' && colChar <= '9'){
            return colChar - '0' + 1;
        }
        else {
            throw new RuntimeException();
        }
    }



    public int getColumn() {
        return column;
    }

    public int getRow() {
        return row;
    }

    public String getCoordinateText() {
        return coordinateText;
    }
}
