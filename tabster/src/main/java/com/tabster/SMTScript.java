package com.tabster;

import java.io.File;
import java.io.InputStream;
import java.io.PrintWriter;
import java.io.Serializable;

import org.apache.commons.io.IOUtils;

import sun.nio.cs.StandardCharsets;

public class SMTScript{
    
    private String script;
    
    public SMTScript(String script) {
        this.script = script;
    }
    
    public String run() throws Exception {
    	// create a temp file    	
    	File f = File.createTempFile("smt", ".smt2");
    	PrintWriter writer = new PrintWriter(f);
    	writer.print(this.script);
    	writer.close();
    	// interact with terminal to check satisfiability and solve SMT Lib String
    	String command = "z3 -smt2 " + f.getAbsolutePath();
    	ProcessBuilder pb = new ProcessBuilder("bash", "-c", command);
    	pb.redirectErrorStream(true);
    	Process shell = pb.start();
    	// To capture output from shell
    	InputStream shellin = shell.getInputStream();
    	// Wait for shell to finish and get the return code
    	shell.waitFor();
    	String response = IOUtils.toString(shellin, StandardCharsets.UTF_8);
    	shellin.close();  
    	return response;
    }
    
}