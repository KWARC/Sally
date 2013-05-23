package info.kwarc.sally.networking.cometd;

public class TemplateRequest {

	String templatePath;
	Object data;
	
	public TemplateRequest(String templatePath, Object data) {
		this.templatePath = templatePath;
		this.data = data;
	}
	
	public Object getData() {
		return data;
	}
	public String getTemplatePath() {
		return templatePath;
	}
	public void setData(Object data) {
		this.data = data;
	}
	public void setTemplatePath(String templatePath) {
		this.templatePath = templatePath;
	}
	
}
