/* 
 * Copyright (C) 2000-2001 Virginia Tech
 *
 * This file is part of JML
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
 * $Id: TreeViewer.java,v 1.1 2003/02/21 15:15:40 flyingroc Exp $
 */

package org.jmlspecs.racwrap.runner; 

import java.awt.*;
import java.awt.event.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.tree.*;

/**
TreeViewer is a swing-based component to view and control checking of classes.
*/
public class TreeViewer extends JPanel 
    implements TreeSelectionListener, ItemListener {

    private Node root = null;
    private JTree jtree = null;
    private JCheckBox wrap = new JCheckBox("wrap");
    private JCheckBox pre = new JCheckBox("pre");
    private JCheckBox post = new JCheckBox("post");
    private JCheckBox inv = new JCheckBox("inv");
    private boolean suppress = false;

    public TreeViewer(Node root) {
        super(new BorderLayout());

        //create the tree
        this.root = root;
        DefaultMutableTreeNode swingRoot = new DefaultMutableTreeNode(root);
        createSwingNodes(root, swingRoot);
        JTree jtree = new JTree(swingRoot);
        jtree.addTreeSelectionListener(this);
        this.jtree = jtree;
        JScrollPane scrollTree = new JScrollPane(jtree);

        //create the checkboxes
        JPanel controller = new JPanel();
        controller.add(wrap);
        controller.add(pre);
        controller.add(post);
        controller.add(inv);

        wrap.addItemListener(this);
        pre.addItemListener(this);
        post.addItemListener(this);
        inv.addItemListener(this);

        this.add(scrollTree, BorderLayout.CENTER);
        this.add(controller, BorderLayout.NORTH);
    }

    public void createSwingNodes(Node parent, DefaultMutableTreeNode swingParent) {
        Enumeration e = parent.getKeys();
        while(e.hasMoreElements()) {
            String key = (String) e.nextElement();
            Node child_node = parent.getChild(key);

            DefaultMutableTreeNode swingChild = null;
            swingChild = new DefaultMutableTreeNode(child_node);
            swingParent.add(swingChild);
            if( ! (child_node instanceof Leaf) ) {
                createSwingNodes(child_node, swingChild);
            }
        }
    }

    /**
        The arguments for the main function are paths to the root
		of a package hierarchy, either a directory, or a jar file.
		Main will display a window cointaining the tree viewer.
    */
    public static void main(String args[]) {
        Node root = TreeBuilder.buildTree(args);
        JFrame frame = new JFrame();
        frame.getContentPane().add(new TreeViewer(root));
        frame.addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                System.exit(0);
            }
        });
        frame.show();
    }

	/**
	This gets called whenever a node is selected in the tree component.
	*/
    public void valueChanged(TreeSelectionEvent e) {
        DefaultMutableTreeNode jNode = null;
        jNode = (DefaultMutableTreeNode) jtree.getLastSelectedPathComponent();
        if(jNode == null)
            return;

        Node n = (Node) jNode.getUserObject();
        
        //we have to do this, because setting the checkboxes generate an event
        suppress = true;
        wrap.setSelected(false);
        pre.setSelected(false);
        post.setSelected(false);
        inv.setSelected(false);

        if(n.isWrap())
            wrap.setSelected(true);
        if(n.isCheckPrecondition())
            pre.setSelected(true);
        if(n.isCheckPostcondition())
            post.setSelected(true);
        if(n.isCheckInvariant())
            wrap.setSelected(true);
        wrap.repaint();
        pre.repaint();
        post.repaint();
        inv.repaint();

        suppress = false;
    }

    /**
	This gets called whenever one of the checkboxes change state.	
    */
    public void itemStateChanged(ItemEvent e) {
        if(suppress)
            return;

        JCheckBox box = (JCheckBox) e.getSource();
        DefaultMutableTreeNode jnode = null;

        jnode = (DefaultMutableTreeNode) jtree.getLastSelectedPathComponent();
        if(jnode == null) {
            suppress = true;
            box.setSelected(false);
            suppress = false;
            return;
        }
        
        Node n = (Node) jnode.getUserObject();
        if(box == wrap) {
            n.setWrap(box.isSelected(),true);
        } else if (box == pre) {
            n.setCheckPrecondition(box.isSelected(),true);
        } else if (box == post) {
            n.setCheckPostcondition(box.isSelected(),true);
        } else if (box == inv) {
            n.setCheckInvariant(box.isSelected(),true);
        }
        jtree.repaint();
    }
}
