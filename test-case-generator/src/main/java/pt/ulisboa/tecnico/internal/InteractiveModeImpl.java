package pt.ulisboa.tecnico.internal;

import pt.ulisboa.tecnico.InteractiveMode;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

/**
 * InteractiveModeImpl halts the execution, until the user presses enter.
 */
public class InteractiveModeImpl implements InteractiveMode{
    public void methodConcolicallyExecuted() {
        System.out.println("Method concolically executed. Press Enter to continue.");
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        try {
            br.readLine();
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                br.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
}
