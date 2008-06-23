package src.utilities;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class ErrorStreamHandler extends Thread {

	private Process p;
	private String messageHeader;
	private String messageFinaliser;
	private boolean quitOnError;
	private boolean quietMode;
	
	public ErrorStreamHandler(Process p, String messageHeader, String messageFinaliser, boolean quitOnError) {
		this.p = p;
		this.messageHeader = messageHeader;
		this.messageFinaliser = messageFinaliser;
		this.quitOnError = quitOnError;
		this.quietMode = false;
	}

	public ErrorStreamHandler(Process p, boolean quitOnError) {
		this.p = p;
		this.messageHeader = null;
		this.messageFinaliser = null;
		this.quitOnError = quitOnError;
		this.quietMode = true;
	}
	
	
	public void run() {
		if(p!=null) {
			try {
				BufferedReader br = new BufferedReader(new InputStreamReader(p.getErrorStream()));
				String line = null;
				while((line = br.readLine())!=null) {

					if(!quietMode) {
						System.out.println(messageHeader);
						System.out.println(line);
					}
					
					while(br.ready()) {
						line = br.readLine();
						if(!quietMode) {
							System.out.println(line);
						}
					}
					
					if(!quietMode) {
						System.out.println(messageFinaliser);
					}
					
					if(p!=null) {
						p.destroy();
						p.waitFor();
					}

					if(quitOnError) {
						System.exit(1);
					}
					
					break;
											
				}
			} catch (IOException ioe) {
				ioe.printStackTrace();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}
}
