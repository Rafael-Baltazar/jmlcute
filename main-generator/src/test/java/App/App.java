package App;

public class App extends AppSuperclass {
    public App app(App a, App b) {
        return a;
    }

    private App nonPublicApp(App a, App b) {
        return a;
    }

    public static App nonInstanceApp(App a, App b) {
        return a;
    }
}