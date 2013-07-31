package info.kwarc.sally.core;

import info.kwarc.sally.core.interfaces.ICookieProvider;

import com.google.inject.Singleton;

@Singleton
public class CookieProvider implements ICookieProvider {
	String cookies;
	String url;
	
	public CookieProvider() {
		cookies = "";
		url = "";
	}
	
	@Override
	public String getCookies() {
		return cookies;
	}
	
	public String getUrl() {
		return url;
	}

	public void setUrl(String url) {
		this.url = url;
	}
	
	@Override
	public void setCookies(String cookies) {
		this.cookies = cookies;		
	}

}
