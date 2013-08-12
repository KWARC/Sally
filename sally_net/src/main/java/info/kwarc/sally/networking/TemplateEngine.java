package info.kwarc.sally.networking;

import java.io.IOException;
import java.io.StringWriter;

import com.google.inject.Singleton;

import freemarker.template.Configuration;
import freemarker.template.Template;
import freemarker.template.TemplateException;

@Singleton
public class TemplateEngine {

	Configuration cfg;
	
	public TemplateEngine() {
		cfg = new Configuration();
		cfg.setClassForTemplateLoading(getClass(), "/sally");
	}
	
	public String generateTemplate(String templatePath, Object data) {
		StringWriter w = new StringWriter();
		Template tpl;
		try {
			tpl = cfg.getTemplate(templatePath);
			tpl.process(data, w);
		} catch (IOException e) {
			e.printStackTrace();
		} catch (TemplateException e) {
			e.printStackTrace();
		}
		return w.toString();
	}
	
	
}
