package samplePackageName;

public class SampleClassName extends SampleSuperclassName {
    public SampleClassName app(SampleClassName a, SampleClassName b) {
        System.out.println("app method");
        return a;
    }

    private SampleClassName nonPublicApp(SampleClassName a, SampleClassName b) {
        System.out.println("nonPublicApp method");
        return a;
    }

    public static SampleClassName nonInstanceApp(SampleClassName a, SampleClassName b) {
        System.out.println("nonInstanceApp method");
        return a;
    }
}