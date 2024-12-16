package controller;

import model.Ship;
import model.Submarine;
import model.player.ComputerPlayer;
import model.player.HumanPlayer;
import model.player.Player;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class Game {

    private final Scanner sc = new Scanner(System.in);

    public Game() {
        String humanPlayerName = getPlayerName();
        List<Ship> fleet = getFleet();

        // Criação dos jogadores com as novas implementações
        Player humanPlayer = new HumanPlayer(humanPlayerName, fleet);
        Player computerPlayer = new ComputerPlayer(fleet);

        playGame(humanPlayer, computerPlayer);
    }

    private String getPlayerName() {
        while (true) {
            System.out.print("Insert the Player's name: ");
            String humanPlayerName = sc.nextLine();

            if (humanPlayerName.equalsIgnoreCase("computer")) {
                System.out.println("This name is already used by your opponent.");
                continue;
            }

            return humanPlayerName.length() > 40 ? humanPlayerName.substring(0, 40) : humanPlayerName;
        }
    }

    private List<Ship> getFleet() {
        List<Ship> fleet = new ArrayList<>();
        for (int i = 0; i < 10; i++) {
            fleet.add(new Submarine());
        }
        return fleet;
    }

    private Player getStartingPlayer(Player player1, Player player2) {
        while (true) {
            System.out.printf("Who starts the game? (h = %s, c = %s): ", player1.getName(), player2.getName());
            String answer = sc.nextLine();

            if (answer.equalsIgnoreCase("h")) return player1;
            if (answer.equalsIgnoreCase("c")) return player2;

            System.out.println("Invalid answer. Please choose 'h' or 'c'.");
        }
    }

    private void playGame(Player player1, Player player2) {
        Player currentPlayer = getStartingPlayer(player1, player2);
        Player opponentPlayer = (currentPlayer == player1) ? player2 : player1;

        while (true) {
            boolean gameOver = false;

            while (!gameOver) {
                currentPlayer.shoot(opponentPlayer.getBoard());
                gameOver = opponentPlayer.getBoard().hasWon();

                if (currentPlayer instanceof HumanPlayer) {
                    currentPlayer.getBoard().showBoard();
                    opponentPlayer.getBoard().showScore(currentPlayer.getName());
                }

                // Troca os jogadores
                Player temp = currentPlayer;
                currentPlayer = opponentPlayer;
                opponentPlayer = temp;
            }

            System.out.printf("%s won the game!%n", opponentPlayer.getName());

            if (getBooleanAnswer("Would you like to see the enemy board? (y/n): ")) {
                opponentPlayer.getBoard().showBoard();
            }

            if (!getBooleanAnswer("Do you want to play again? (y/n): ")) break;

            // Reinicia o estado do jogo
            player1.resetPlayer();
            player2.resetPlayer();
        }
    }

    private boolean getBooleanAnswer(String question) {
        while (true) {
            System.out.print(question);
            String answer = sc.nextLine();

            if (answer.equalsIgnoreCase("y")) return true;
            if (answer.equalsIgnoreCase("n")) return false;

            System.out.println("Invalid answer. Please choose 'y' or 'n'.");
        }
    }
}
