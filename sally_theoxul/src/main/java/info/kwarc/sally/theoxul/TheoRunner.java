/**
 * 
 */
package info.kwarc.sally.theoxul;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author cdavid
 * 
 */
public class TheoRunner implements Runnable {

	private Process externalProcess = null;
	String xulRunnerPath;
	String applicationPath;
	Boolean debug;
	Logger log;
	Boolean isRunning;

	public TheoRunner(String xulRunnerPath, String applicationPath) {
		this(xulRunnerPath, applicationPath, false);
	}

	public TheoRunner(String xulRunnerPath, String applicationPath, Boolean debug) {
		log = LoggerFactory.getLogger(getClass());
		this.xulRunnerPath = xulRunnerPath;
		this.applicationPath = applicationPath;
		this.debug = debug;
		isRunning = false;
	}

	public void stop() {
	}

	private void executeCmd(String args) {
		try {
			log.debug("About to run \n"+ args);
			this.externalProcess = Runtime.getRuntime().exec(args);
			// using this:
			// http://stackoverflow.com/questions/1732455/redirect-process-output-to-stdout
			StreamOutput err = new StreamOutput(this.externalProcess.getErrorStream());
			StreamOutput out = new StreamOutput(this.externalProcess.getInputStream());
			err.start();
			out.start();
			isRunning = true;
			externalProcess.waitFor();
			isRunning = false;
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}

	public void run() {
		String params = this.xulRunnerPath + " -app " + "" + this.applicationPath + ""; 
		if (debug)
			params += " -jsconsole";
		executeCmd(params);
	}
	
	public Boolean getIsRunning() {
		return isRunning;
	}
}

class StreamOutput extends Thread {

	InputStream is;
	Logger log;

	public StreamOutput(InputStream is) {
		this.is = is;
		log = LoggerFactory.getLogger(StreamOutput.class);
	}

	@Override
	public void run() {
		BufferedReader br = new BufferedReader(new InputStreamReader(is));
		String read = null;
		try {
			while ((read = br.readLine()) != null) {
				log.debug(read);
			}
		} catch (IOException e) {
			log.debug(e.getMessage());
		}
	}	
}
