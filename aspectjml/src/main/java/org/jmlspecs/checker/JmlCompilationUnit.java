/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler and the JML Project.
 *
 * based in part on work:
 *
 * Copyright (C) 1990-99 DMS Decision Management Systems Ges.m.b.H.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 * $Id: JmlCompilationUnit.java,v 1.48 2007/02/08 14:05:49 leavens Exp $
 */

package org.jmlspecs.checker;

import java.io.File;
import java.util.ArrayList;

import org.multijava.mjc.CCompilationUnit;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CompilerPassEnterable;
import org.multijava.mjc.JClassOrGFImportType;
import org.multijava.mjc.JCompilationUnit;
import org.multijava.mjc.JCompilationUnitType;
import org.multijava.mjc.JPackageImportType;
import org.multijava.mjc.JPackageName;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.MJGenericFunctionDecl;
import org.multijava.mjc.Main;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.Destination;
import org.multijava.util.Utils;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents a single JML compilation unit (typically a file
 * in a file-based compiler like this) in the AST.  The production for a
 * compilation unit is the main entry point in JML parser grammar.
 */
public class JmlCompilationUnit extends JmlNode
        implements JCompilationUnitType {
    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a CompilationUnit with the specified top level context
     *
     * @param refinePrefix     the refine-prefix annotation for this c.u.
     * @param where            the position of this token
     * @param packageName      the package to which this c.u. belongs
     * @param importedPackages the packages imported by this c.u.
     * @param importedUnits    the classes and external members imported by
     *                         this compilation unit
     * @param typeDeclarations the classes and interfaces declared
     *                         in this c.u.
     * @param tlMethods        the MultiJava top-level declarations
     *                         in this c.u.
     */
    public JmlCompilationUnit( /*@non_null*/ TokenReference where,
                   /*@non_null*/ JPackageName packageName,
                   /*@non_null*/ CCompilationUnit export,
			       /*@non_null*/ JPackageImportType[] importedPackages,
			       /*@non_null*/ ArrayList importedUnits,
			       /*@non_null*/ JTypeDeclarationType[] typeDeclarations,
			       /*@non_null*/ ArrayList tlMethods, //of MJTopLevelMethodDeclaration
			       /*@nullable*/ JmlRefinePrefix refinePrefix
    ) {
        super(where);        // cache the token reference in the superclass
        this.delegee =
                new JCompilationUnit(where, packageName, export,
                        importedPackages, importedUnits,
                        typeDeclarations, tlMethods);
        this.refinePrefix = refinePrefix;

        if (where != null) {
            // PChalin: I don't see how where could be null since the
            // constructor to JCompilationUnit (invoked above) will throw a
            // null pointer exception if where is null.
            //
            // this is only needed so the junit parser tests won't in
            // some rare cases get null pointer exceptions!
            levelNumber = JmlSourceClass.computeSuffixNumber(where.name());
        }

    }

    // ACCESSORS
    // ----------------------------------------------------------------------

    public /*@non_null@*/ String packageNameAsString() {
        return delegee.packageNameAsString();
    }

    public /*@non_null@*/ File file() {
        return delegee.file();
    }

    public /*@non_null@*/ String getFilePath() {
        return Utils.getFilePath(file());
    }

    public /*@non_null@*/ String fileNameIdent() {
        return delegee.fileNameIdent();
    }

    public /*@non_null*/ JPackageName packageName() {
        return delegee.packageName();
    }

    public void setPackage(/*@non_null*/ JPackageName packageName) {
        delegee.setPackage(packageName);
    }

    public /*@non_null*/ JPackageImportType[] importedPackages() {
        return delegee.importedPackages();
    }

    public void setImportedPackages(/*@non_null*/ JPackageImportType[] packages) {
        delegee.setImportedPackages(packages);
    }

    public /*@non_null*/ JClassOrGFImportType[] importedClasses() {
        return delegee.importedClasses();
    }

    public /*@ pure non_null @*/ JTypeDeclarationType[] typeDeclarations() {
        return delegee.typeDeclarations();
    }

    public /*@non_null*/ MJGenericFunctionDecl[] gfDeclarations() {
        return delegee.gfDeclarations();
    }

    /**
     * Returns the CSourceClass objects representing the type
     * signatures of the types declared in this compilatoin unit
     * <em>and as nested types</em>.
     */
    public /*@non_null*/ CSourceClass[] allTypeSignatures() {
        return delegee.allTypeSignatures();
    }


    /**
     * Returns true iff this compilation unit contains a declaration
     * for a top-level type with the given fully qualified name.
     *
     * @param qualifiedName a fully qualified name with parts
     *                      separated by '/' not '.'
     */
    public boolean declaresType(/*@non_null@*/ String qualifiedName) {
        return delegee.declaresType(qualifiedName);
    }

    /**
     * Returns true iff this compilation unit contains a declaration
     * for a generic function with the given fully qualified name.
     *
     * @param qualifiedName a fully qualified name with parts
     *                      separated by '/' not '.'
     */
    public boolean declaresGF(/*@non_null@*/ String qualifiedName) {
        return delegee.declaresGF(qualifiedName);
    }

    public /*@non_null*/ ArrayList tlMethods() {
        return delegee.tlMethods();
    }

    public /*@non_null*/ JClassOrGFImportType[] importedGFs() {
        return delegee.importedGFs();
    }

    public /*@non_null*/ JClassOrGFImportType[] importedUnits() {
        return delegee.importedUnits();
    }

    public /*@ nullable */ JmlCompilationUnit refiningCUnit() {
        return (JmlCompilationUnit) refiningCUnit;
    }

    public /*@ nullable */ JmlCompilationUnit refinedCUnit() {
        if (refinePrefix == null) {
            return null;
        } else {
            return (JmlCompilationUnit) refinePrefix.refinedCUnit();
        }
    }

    public /*@ nullable */ Main.Task getSuspendedTask() {
        return task;
    }

    public void setSuspendedTask(/*@nullable@*/ Main.Task task) {
        this.task = task;
    }

    public /*@ nullable */ JmlRefinePrefix refinePrefix() {
        return refinePrefix;
    }

    /**
     * Returns true if this compilation is refined by another
     * compilation unit.
     */
    public boolean isRefined() {
        return refined;
    }

    /**
     * Returns true if this compilation unit has finished the
     * checkInitializers phase.
     */
    public boolean isSymbolTableFinished() {
        return finishedSymTab;
    }

    /**
     * Returns true if this compilation unit has finished the
     * typecheck phase.
     */
    public boolean isTypeCheckFinished() {
        return finishedTypeCheck;
    }

    public void setRefiningCUnit(/*@non_null@*/ JmlCompilationUnit refiningCUnit) {
        this.refiningCUnit = refiningCUnit;
        refined = true;
    }

    /**
     * Sets that this compilation is refined by another compilation
     * unit.
     */
    public void setRefined() {
        refined = true;
    }

    /**
     * Returns true if this compilation unit has a Java source file
     * in the refinement chain. This method should be called after
     * typechecking.
     */
    public boolean hasSourceInRefinement() {
        if (levelNumber == 3) { // *.java
            return true;
        }
        JmlCompilationUnit refined = refinedCUnit();
        if (refined != null) {
            return refined.hasSourceInRefinement();
        }
        return false;
    }

    // ---------------------------------------------------------------------
    // REVISE AST FOR MULTIJAVA
    // ---------------------------------------------------------------------

    /**
     * Performs preliminary processing on compilation units and types.
     * Processes type imports so external methods' receiver types can
     * be analyzed and supertypes can be resolved.  Groups external
     * methods by name, corresponding to the anchor classes that will
     * eventually be generated.  Mutates the name space management in
     * CTopLevel to record a CGenericFunctionCollection singleton for
     * each anchor class.
     */
    public void preprocessDependencies( /*@non_null@*/ org.multijava.mjc.Main compiler)
            throws PositionedError {
        if (refinePrefix != null) {
            refinePrefix.setPackageName(delegee.packageNameAsString());
            refinePrefix.checkLevelNumber(levelNumber);
            refinePrefix.preprocessDependencies(compiler);
            refinePrefix.preprocessRefinedTypes(this);

            JCompilationUnitType refinedCUnit = refinePrefix.refinedCUnit();
            if (refinedCUnit != null) {
                // refinedCUnit is null when the file refined is a
                // ".class" file.
                ((JmlCompilationUnit) refinedCUnit).setRefiningCUnit(this);
            }
        }
        delegee.preprocessDependencies(compiler);
    }

    /**
     * Compares this to a given object.
     * <p/>
     * <pre><jml>
     * also
     *   requires o instanceof JmlCompilationUnit;
     *   ensures (* \result is ordered according to suffix of the source files *);
     * also
     *   requires o != null && !(o instanceof JmlCompilationUnit);
     *   signals_only ClassCastException;
     * </jml></pre>
     *
     * @param o an <code>Object</code> value to compare to this
     * @return 0 if this.equals(o)
     * @throws ClassCastException if <code>o</code> is incomparable to this
     */
    public int compareTo(/*@ non_null @*/ Object o) throws ClassCastException {
        JmlCompilationUnit other = (JmlCompilationUnit) o;
        int res = delegee.compareTo(other.delegee);
        if (res == 0) {
            res = this.levelNumber - other.levelNumber;
        }
        return res;
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------

    public void checkInterface( /*@non_null@*/ org.multijava.mjc.Main compiler)
            throws PositionedError {
        if (refinePrefix != null) {
            refinePrefix.checkInterface();
        }
        delegee.checkInterface(compiler);
        if (isRefined()) {
            JmlTypeLoader.getJmlSingleton()
                    .activatePartiallyProcessedTask(refiningCUnit);
        }
    }

    public void checkInitializers( /*@non_null@*/ org.multijava.mjc.Main compiler)
            throws PositionedError {
        delegee.checkInitializers(compiler);
        finishedSymTab = true;
    }

    /**
     * Resolves value specializer expressions to the compile-time
     * constants they represent.  Must come after the
     * checkInitializers phase.
     *
     * @param compiler the compiler that is calling (passed down
     *                 through the AST via CContextType subtypes
     *                 and used for error reporting)
     */
    void resolveSpecializers(/*@non_null@*/ org.multijava.mjc.Main compiler)
            throws PositionedError {
        delegee.resolveSpecializers(compiler);
    }


    // ----------------------------------------------------------------------
    // CODE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Finds the top method of every declared method.  Called after
     * the checkInitializers pass.  This cannot be done before then
     * because the external generic function mappings are not complete
     * until the end of the checkInterface pass and the constant value
     * specializers are not known until after the checkInitializers
     * pass.  This must be done before the typecheck pass so that all
     * specialized argument positions for generic functions are known
     * for ambiguity checking.
     */
    public void resolveTopMethods() throws PositionedError {
        delegee.resolveTopMethods();
    }

    public void typecheck(/*@non_null@*/ org.multijava.mjc.Main compiler)
            throws PositionedError {
        try {
            delegee.typecheck(compiler);
        } catch (RuntimeException e) {
//		maybe this should be removed at some point (just to guarantee) --- [[[hemr]]]
        }
        //System.out.println("typechecking " + delegee.file().getName()+" done");
        finishedTypeCheck = true;
    }

    public void checkAssignableClauses() throws PositionedError {
        JTypeDeclarationType[] typeDecls = combinedTypeDeclarations();
        for (int i = 0; i < combinedTypeDeclarations.length; i++) {
            JmlTypeDeclaration typeDecl = (JmlTypeDeclaration) typeDecls[i];
            typeDecl.checkAssignableClauses();
        }
    }

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    public void translateMJ( /*@non_null@*/ org.multijava.mjc.Main compiler) {
        delegee.translateMJ(compiler);
    }

    /**
     * Accepts the specified visitor.
     *
     * @param p the visitor
     */
    public void accept( /*@non_null@*/ MjcVisitor p) {
        if (p instanceof JmlVisitor)
            ((JmlVisitor) p).visitJmlCompilationUnit(this);
        else
            throw new UnsupportedOperationException(
                    JmlNode.MJCVISIT_MESSAGE);
    }

    public void acceptDelegee( /*@non_null@*/ MjcVisitor p) {
        p.visitCompilationUnit(delegee);
    }

    public void combineSpecifications() {
        if (combinedTypeDeclarations == null) {
            combinedTypeDeclarations = typeDeclarations();
            if (refinePrefix != null) {
                for (int i = 0; i < combinedTypeDeclarations.length; i++) {
                    JmlTypeDeclaration typeDecl
                            = (JmlTypeDeclaration) combinedTypeDeclarations[i];
                    typeDecl.setMembersToCombinedMembers();
                }
            }
        }
    }

    public /*@non_null*/ JTypeDeclarationType[] combinedTypeDeclarations() {
        combineSpecifications();
        return combinedTypeDeclarations;
    }

    // -------------------------------------------------------------
    // CompilerPassEnterable
    // -------------------------------------------------------------


    //@ protected represents arePassParametersCached <- arePassParametersCached();

    /*@ protected pure model boolean arePassParametersCached() {
      @    return cachedCompiler == null;
      @ }
      @*/

    /**
     * Caches the arguments for the compiler passes.
     *
     * @see CompilerPassEnterable
     * <p/>
     * <pre><jml>
     * also
     *   ensures arePassParametersCached;
     * </jml></pre>
     */
    public void cachePassParameters( /*@non_null@*/ org.multijava.mjc.Main compiler, 
				     /*@non_null@*/ Destination destination) {
        cachedCompiler = compiler;
        //cachedDestination = destination;
    }

    /**
     * Performs preliminary processing on compilation units and types.
     * Processes type imports so external methods' receiver types can
     * be analyzed and supertypes can be resolved.  Groups external
     * methods by name, corresponding to the anchor classes that will
     * eventually be generated.  Mutates the name space management in
     * CTopLevel to record a CGenericFunctionCollection singleton for
     * each anchor class.
     */
    public void preprocessDependencies() throws PositionedError {
        preprocessDependencies(cachedCompiler);
    }

    public void checkInterface() throws PositionedError {
        checkInterface(cachedCompiler);
    }

    public void checkInitializers() throws PositionedError {
        checkInitializers(cachedCompiler);
    }

    public void resolveSpecializers() throws PositionedError {
        resolveSpecializers(cachedCompiler);
    }

    public void typecheck() throws PositionedError {
        typecheck(cachedCompiler);
    }

    public void translateMJ() {
        translateMJ(cachedCompiler);
    }

    // ----------------------------------------------------------------------
    // PUBLIC DATA MEMBERS
    // ----------------------------------------------------------------------

    public static final /*@non_null@*/ JPackageImportType JMLSPECS_LANG =
            new JmlPackageImport(org.multijava.util.compiler.TokenReference.NO_REF,
                    "org/jmlspecs/lang",
                    null, true);

    static {
        // needed to avoid a warning message
        JMLSPECS_LANG.setClassUsed("JMLDataGroup");
    }

    // ----------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------------

    private /*@non_null@*/ org.multijava.mjc.Main cachedCompiler;
    //  private Destination cachedDestination;

    /**
     * The MultiJava compilation unit decorated by this JML class.
     */
    private /*@ non_null */ JCompilationUnit delegee;

    private /*@ nullable */ JmlRefinePrefix refinePrefix;

    private /*@ nullable */ JTypeDeclarationType[] combinedTypeDeclarations = null;

    /**
     * See {@link JmlSourceClass} for an explanation of
     * the levelNumber field
     */
    protected int levelNumber = -1;

    /**
     * True if this compilation unit is refined by another compilation
     * unit.
     */
    private boolean refined = false;

    private boolean finishedSymTab = false;
    private boolean finishedTypeCheck = false;

    private /*@ nullable */ JmlCompilationUnit refiningCUnit = null;

    private /*@ nullable */ Main.Task task = null;
}
