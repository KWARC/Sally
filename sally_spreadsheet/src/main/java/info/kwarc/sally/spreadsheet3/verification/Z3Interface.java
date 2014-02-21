package info.kwarc.sally.spreadsheet3.verification;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Interface to Z3. Z3 must be installed and the environment variable Z3_HOME must be set. 
 * @author cliguda
 *
 */
public class Z3Interface {
	
	final Logger logger = LoggerFactory.getLogger(Z3Interface.class);
	
	private BufferedReader reader = null;
	private BufferedWriter writer = null;
	
	List<String> completeSpecification = new ArrayList<String>();
	
	/**
	 * Creates an interface for a specification. 
	 * Different interfaces for independent verification tasks should be used.
	 */
	public Z3Interface() {
		List<String> commands = new ArrayList<String>();
		String z3Path = System.getenv("Z3_HOME");
		if (z3Path.isEmpty())
			logger.error("Can not find Z3. Verification aborted.");
		else {
			commands.add(z3Path + "/bin/z3");
		    commands.add("/smt2");
		    commands.add("/in");
		    
		    ProcessBuilder builder = new ProcessBuilder(commands);
		    builder.redirectErrorStream(true);
		   	try {
				Process process  = builder.start();
				reader = new BufferedReader(new InputStreamReader(process.getInputStream())); 
				writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
			} catch (IOException e) {
				logger.error("Can not start Z3. Verification aborted.");
			} 
		}
	}
	
	/**
	 * Verifies the list of statements.
	 * @param statements
	 * @param temporary Should the list of statements be added to the specification temporary or permanent.
	 * @return
	 */
	public VerificationStatusIntern verify(List<String> statements, boolean temporary) {
		if (temporary)
			writeSpec("(push)\n");
		
		writeSpec(statements);
		VerificationStatusIntern status = isSat();
		
		if (temporary)
			writeSpec("(pop)\n");
		
		return status;
	}
	
	public VerificationStatusIntern verify(String statement, boolean temporary) {
		List<String> statements = new ArrayList<String>();
		statements.add(statement);
		return verify(statements, temporary);
	}
	
	/**
	 * Checks if the current specification is satisfiable.
	 * @return
	 */
	public VerificationStatusIntern isSat() {		
		VerificationStatusIntern status = null;
		
		if (writeSpec("(check-sat)\n") && (reader != null) ) {
			List<String> output = new ArrayList<String>();
			try {
				output.add(reader.readLine());
				while (reader.ready())
					output.add(reader.readLine());
			} catch (IOException e) {
				logger.error("Communication with Z3 failed. Verification aborted.");
			}
			if ((output.size() != 1) || ( !output.get(0).equals("sat") && !output.get(0).equals("unsat") ) ) {
				logger.error("Verification failed.");
				for (String s : output)
					logger.info("[Z3 Output] " + s);
				printCompleteSpecification();
				status = VerificationStatusIntern.ERROR;
			} else if (output.get(0).equals("sat"))
				status = VerificationStatusIntern.SAT;
			else
				status = VerificationStatusIntern.UNSAT;
		
		} else
			status = VerificationStatusIntern.ERROR;
		
		return status;
	}
	
	public void printCompleteSpecification() {
		System.out.println("Complete Specification");
		for (String s : completeSpecification)
			System.out.println(s);
		System.out.println("--------------");
	}
	
	 private boolean writeSpec(List<String> commands) {
		 boolean succeed = false;
		 
		 if (writer != null) {
			try {
				for (String cmd : commands) {
					writer.write(cmd);
					completeSpecification.add(cmd);
				}
				writer.flush();
				succeed = true;
			} catch (IOException e) {
				logger.error("Communication with Z3 failed. Verification aborted.");
			}
		 }
		 return succeed;
	 }
	 
	 private boolean writeSpec(String command) {
		 List<String> commands = new ArrayList<String>();
		 commands.add(command);
		 return writeSpec(commands);
	 }

}
