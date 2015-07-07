package samplePackageName;

/**
 * Uses threads that deadlock.
 */
public class DeadlockExample {
    private Object a = new Object(), b = new Object();

    public void start() {
        new ThreadAB().start();
        new ThreadBA().start();
    }

    private class ThreadAB extends Thread implements Runnable {
        @Override
        public void run() {
            synchronized (a) {
                synchronized (b) {
                    System.out.println("I have a and b locks.");
                }
            }
        }
    }

    private class ThreadBA extends Thread implements Runnable {
        @Override
        public void run() {
            synchronized (b) {
                synchronized (a) {
                    System.out.println("I have b and a locks.");
                }
            }
        }
    }
}
