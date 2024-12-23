package model;

public enum Fields {
    A(1),
    B(2),
    C(3),
    D(4),
    E(5),
    F(6),
    G(7),
    H(8),
    I(9),
    J(10);

    int rowTitle;

    Fields(int rowTitle) {
        this.rowTitle = rowTitle;
    }

    public static boolean containsRow (String row) {
        for (Fields rowField : values()) {
            if (rowField.toString().equals(row)) return true;
        }
        return false;
    }

    //@ requires input.length() == 1;
    public static boolean containsColumn (String input) {
        int numberRows = values().length;
        try {

            int column = Integer.parseInt(input);
            return column >= 0 && column <= numberRows + 1;
        } catch (Error e) {
            return false;
        }
    }

    public static String getRowLetter (int rowIndex) {
        for (Fields rowField : values()) {
            if (rowField.rowTitle == rowIndex) return rowField.toString();
        }
        throw new RuntimeException();
    }
}
