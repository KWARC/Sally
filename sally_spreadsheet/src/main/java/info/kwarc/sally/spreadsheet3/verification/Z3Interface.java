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

public class Z3Interface {
	
	public enum VerificationStatus {
		SAT, UNSAT, FAILED
	}
	
	final Logger logger = LoggerFactory.getLogger(Z3Interface.class);
	
	private BufferedReader reader = null;
	private BufferedWriter writer = null;
	
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
	
	public VerificationStatus verify(List<String> statements, boolean temporary) {
		if (temporary)
			writeSpec("(push)\n");
		
		writeSpec(statements);
		VerificationStatus status = isSat();
		
		if (temporary)
			writeSpec("(pop)\n");
		
		return status;
	}
	
	public VerificationStatus verify(String statement, boolean temporary) {
		List<String> statements = new ArrayList<String>();
		statements.add(statement);
		return verify(statements, temporary);
	}
	
	public VerificationStatus isSat() {		
		VerificationStatus status = null;
		
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
				status = VerificationStatus.FAILED;
			} else if (output.get(0).equals("sat"))
				status = VerificationStatus.SAT;
			else
				status = VerificationStatus.UNSAT;
		
		} else
			status = VerificationStatus.FAILED;
		
		return status;
	}
	
	 private boolean writeSpec(List<String> commands) {
		 boolean succeed = false;
		 
		 if (writer != null) {
			try {
				for (String cmd : commands)
					writer.write(cmd);
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
