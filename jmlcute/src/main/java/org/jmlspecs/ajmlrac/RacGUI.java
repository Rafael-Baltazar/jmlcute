// Generated from RacGUI.gui
package org.jmlspecs.ajmlrac;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;

import javax.swing.JFileChooser;

import org.multijava.util.Options;
import org.multijava.util.gui.GUIOutputWindow;
import org.multijava.util.gui.GUIUtil;

/** This class is automatically generated from RacGUI.gui
 *  and contains member fields corresponding to tool-specific GUI specifications.
 */
public class RacGUI extends org.multijava.util.gui.GUI {


  public static void main(String[] args) {
    init(args, true);
  }


  public static RacGUI init(String[] args, boolean standAlone) {
    RacOptions options = new RacOptions();
    ArrayList infiles = new ArrayList();
//    ArrayList extraArguments = new ArrayList();
    boolean commandLine = false;
    if (args.length != 0) {
      commandLine = true;
      new Main().runParser(args, options, infiles);
    }
    return new RacGUI(options, infiles, commandLine, standAlone);
  }


  public RacGUI(Options options, ArrayList infiles, boolean commandLine, boolean standAlone) {
    super("Rac", options, infiles, commandLine, standAlone);
  }


  public void interruptCompilation() {
    Main.interruptCompilation();
  }


  protected boolean dirInClassPath(Options opt, String dir) {
    if (((RacOptions)opt).sourcepath() != null) {
      return GUIUtil.dirInPath(((RacOptions)opt).sourcepath(), dir);
    } else if (((RacOptions)opt).classpath() != null) {
      return GUIUtil.dirInPath(((RacOptions)opt).classpath(), dir);
    } else {
      return false;
    }
  }


  protected String getClasspath(Options opt) {
    return ((RacOptions)opt).classpath();
  }


  protected String getSourcepath(Options opt) {
    return ((RacOptions)opt).sourcepath();
  }


  protected OpenHandler createOpenHandlerInstance() {
    return new RacOpenHandler();
  }


  protected Compilation createCompilationInstance(String[] files, Options opt, OutputStream os) {
    return new RacCompilation(files, (RacOptions)opt, os);
  }


  protected String getWebpageName() {
    return "JML Web Page";
  }


  protected String getWebpageLocation() {
    return "http://www.jmlspecs.org";
  }


  protected GUIOutputWindow createOutputWindow(InputStream is) {
    return new GUIOutputWindow(this, is);
  }


  protected class RacOpenHandler extends OpenHandler {
    protected RacOpenHandler() {
    }
    protected JFileChooser createFileChooser() {
      JFileChooser fileChooser = super.createFileChooser();
      AllFilesGUIFileFilter all = new AllFilesGUIFileFilter();
      fileChooser.addChoosableFileFilter(all);
      fileChooser.addChoosableFileFilter(new RacGUIFileFilter(".jml"));
      fileChooser.addChoosableFileFilter(new RacGUIFileFilter(".refines-jml"));
      fileChooser.addChoosableFileFilter(new RacGUIFileFilter(".jml-refined"));
      fileChooser.addChoosableFileFilter(new RacGUIFileFilter(".spec"));
      fileChooser.addChoosableFileFilter(new RacGUIFileFilter(".refines-spec"));
      fileChooser.addChoosableFileFilter(new RacGUIFileFilter(".spec-refined"));
      fileChooser.addChoosableFileFilter(new RacGUIFileFilter(".java"));
      fileChooser.addChoosableFileFilter(new RacGUIFileFilter(".refines-java"));
      fileChooser.addChoosableFileFilter(new RacGUIFileFilter(".java-refined"));
      fileChooser.setFileFilter(all);
      return fileChooser;
    }
  }


  protected class AllFilesGUIFileFilter extends GUIFileFilter {
    public boolean hasActiveSuffix(String name) {
      return name.endsWith(".jml")
        || name.endsWith(".refines-jml")
        || name.endsWith(".jml-refined")
        || name.endsWith(".spec")
        || name.endsWith(".refines-spec")
        || name.endsWith(".spec-refined")
        || name.endsWith(".java")
        || name.endsWith(".refines-java")
        || name.endsWith(".java-refined");
    }
    public String getDescription() {
      return "JML Readable Files";
    }
  }


  protected class RacGUIFileFilter extends GUIFileFilter {
    String suffix;
    public RacGUIFileFilter(String suffix) {
      this.suffix = suffix;
    }
    public boolean hasActiveSuffix(String name) {
      return name.endsWith(suffix);
    }
    public String getDescription() {
      return suffix;
    }
  }


  protected class RacCompilation extends Compilation implements Runnable {
    private String[] files;
    private RacOptions options;
    private OutputStream os;

    protected RacCompilation(String[] files, RacOptions options, OutputStream os) {
      this.files = files;
      this.options = options;
      this.os = os;
    }

    public void run() {
      Main.compile(files, options, os);
    }
  }


}
