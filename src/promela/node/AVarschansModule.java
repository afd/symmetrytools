/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class AVarschansModule extends PModule
{
    private POneDecl _oneDecl_;

    public AVarschansModule()
    {
        // Constructor
    }

    public AVarschansModule(
        @SuppressWarnings("hiding") POneDecl _oneDecl_)
    {
        // Constructor
        setOneDecl(_oneDecl_);

    }

    @Override
    public Object clone()
    {
        return new AVarschansModule(
            cloneNode(this._oneDecl_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAVarschansModule(this);
    }

    public POneDecl getOneDecl()
    {
        return this._oneDecl_;
    }

    public void setOneDecl(POneDecl node)
    {
        if(this._oneDecl_ != null)
        {
            this._oneDecl_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._oneDecl_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._oneDecl_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._oneDecl_ == child)
        {
            this._oneDecl_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._oneDecl_ == oldChild)
        {
            setOneDecl((POneDecl) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
